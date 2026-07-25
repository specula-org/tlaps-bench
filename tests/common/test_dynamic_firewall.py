"""Focused tests for the dnsmasq/ipset firewall mode."""

import os
import stat
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DOCKERFILE = REPO_ROOT / "docker" / "base.Dockerfile"
FIREWALL_SH = REPO_ROOT / "docker" / "firewall.sh"


def _stub(bindir, name, body):
    path = bindir / name
    path.write_text(f"#!/bin/bash\nset -e\n{body}\n")
    path.chmod(path.stat().st_mode | stat.S_IEXEC)


def _run_dynamic_firewall(
    tmp_path,
    hosts="api2.cursor.sh, *.api5.cursor.sh",
    resolvers="nameserver 127.0.0.11\noptions ndots:0\n",
):
    bindir = tmp_path / "bin"
    bindir.mkdir()
    logs = {}
    for tool in ("iptables", "ip6tables", "ipset", "dnsmasq"):
        log = tmp_path / f"{tool}.log"
        log.write_text("")
        logs[tool] = log
        _stub(bindir, tool, f'printf "%s\\n" "$*" >> "{log}"')
    _stub(
        bindir,
        "id",
        'if [ "$1" = "-u" ] && [ "$2" = "tlaps-dnsmasq" ]; then echo 4242; else exec /usr/bin/id "$@"; fi',
    )

    resolv_conf = tmp_path / "resolv.conf"
    resolv_conf.write_text(resolvers)
    env = {
        **os.environ,
        "PATH": f"{bindir}:{os.environ['PATH']}",
        "DYNAMIC_FIREWALL": "1",
        "FIREWALL_HOSTS": hosts,
        "RESOLV_CONF": str(resolv_conf),
    }
    result = subprocess.run(
        ["bash", str(FIREWALL_SH)],
        capture_output=True,
        text=True,
        env=env,
        timeout=30,
    )
    calls = {tool: path.read_text().splitlines() for tool, path in logs.items()}
    return result, calls, resolv_conf.read_text()


def test_image_installs_dynamic_firewall_tools_and_dedicated_user():
    contents = DOCKERFILE.read_text()

    assert "dnsmasq-base ipset" in contents
    assert "groupadd --system tlaps-dnsmasq" in contents
    assert "--gid tlaps-dnsmasq" in contents
    assert "--shell /usr/sbin/nologin tlaps-dnsmasq" in contents


def test_dynamic_mode_configures_allowlisted_dns_and_ipset(tmp_path):
    result, calls, resolv_conf = _run_dynamic_firewall(tmp_path)

    assert result.returncode == 0, result.stderr
    assert calls["ipset"] == ["-exist create tlaps-egress-v4 hash:ip family inet maxelem 65536"]
    dnsmasq = calls["dnsmasq"][0]
    for required in (
        "--conf-file=",
        "--no-resolv",
        "--no-hosts",
        "--bind-interfaces",
        "--listen-address=127.0.0.1",
        "--user=tlaps-dnsmasq",
        "--group=tlaps-dnsmasq",
        "--stop-dns-rebind",
        "--filter-AAAA",
        "--address=/#/",
        "--server=/api2.cursor.sh/127.0.0.11",
        "--ipset=/api2.cursor.sh/tlaps-egress-v4",
        "--server=/api5.cursor.sh/127.0.0.11",
        "--ipset=/api5.cursor.sh/tlaps-egress-v4",
    ):
        assert required in dnsmasq
    assert resolv_conf == "nameserver 127.0.0.1\noptions ndots:0\n"


def test_dynamic_mode_uses_all_ipv4_resolvers(tmp_path):
    result, calls, _ = _run_dynamic_firewall(
        tmp_path,
        hosts="api2.cursor.sh",
        resolvers=(
            "nameserver 2001:db8::53\n"
            "nameserver 999.0.0.1\n"
            "nameserver 127.0.0.11\n"
            "nameserver 127.0.0.11\n"
            "nameserver 10.0.0.53"
        ),
    )

    assert result.returncode == 0, result.stderr
    dnsmasq = calls["dnsmasq"][0]
    assert dnsmasq.count("--server=/api2.cursor.sh/127.0.0.11") == 1
    assert dnsmasq.count("--server=/api2.cursor.sh/10.0.0.53") == 1
    assert "2001:db8::53" not in dnsmasq
    assert "999.0.0.1" not in dnsmasq
    for resolver in ("127.0.0.11", "10.0.0.53"):
        udp_rule = f"-A OUTPUT -p udp -d {resolver} --dport 53 -m owner --uid-owner 4242 -j ACCEPT"
        tcp_rule = f"-A OUTPUT -p tcp -d {resolver} --dport 53 -m owner --uid-owner 4242 -j ACCEPT"
        assert calls["iptables"].count(udp_rule) == 1
        assert calls["iptables"].count(tcp_rule) == 1


def test_dynamic_mode_seals_direct_dns_and_blocks_private_before_ipset(tmp_path):
    result, calls, _ = _run_dynamic_firewall(tmp_path)

    assert result.returncode == 0, result.stderr
    rules = calls["iptables"]
    udp_upstream = "-A OUTPUT -p udp -d 127.0.0.11 --dport 53 -m owner --uid-owner 4242 -j ACCEPT"
    tcp_upstream = "-A OUTPUT -p tcp -d 127.0.0.11 --dport 53 -m owner --uid-owner 4242 -j ACCEPT"
    assert udp_upstream in rules
    assert tcp_upstream in rules
    assert "-A OUTPUT -p udp -d 127.0.0.1 --dport 53 -j ACCEPT" in rules
    assert "-A OUTPUT -p tcp -d 127.0.0.1 --dport 53 -j ACCEPT" in rules

    udp_dns_drop = rules.index("-A OUTPUT -p udp --dport 53 -j DROP")
    tcp_dns_drop = rules.index("-A OUTPUT -p tcp --dport 53 -j DROP")
    loopback_allow = rules.index("-A OUTPUT -o lo -j ACCEPT")
    assert rules.index(udp_upstream) < udp_dns_drop < loopback_allow
    assert rules.index(tcp_upstream) < tcp_dns_drop < loopback_allow

    ipset_allow = rules.index("-A OUTPUT -m set --match-set tlaps-egress-v4 dst -p tcp --dport 443 -j ACCEPT")
    for network in (
        "10.0.0.0/8",
        "100.64.0.0/10",
        "169.254.0.0/16",
        "172.16.0.0/12",
        "192.168.0.0/16",
    ):
        assert rules.index(f"-A OUTPUT -d {network} -j DROP") < ipset_allow
    assert rules[-1] == "-A OUTPUT -j DROP"
    assert calls["ip6tables"] == ["-P OUTPUT DROP"]


def test_dynamic_mode_rejects_malformed_allowlist_entries(tmp_path):
    result, calls, resolv_conf = _run_dynamic_firewall(
        tmp_path,
        hosts="api2.cursor.sh/../../etc/passwd",
    )

    assert result.returncode == 1
    assert "invalid dynamic firewall hostname" in result.stderr
    assert calls["dnsmasq"] == []
    assert resolv_conf == "nameserver 127.0.0.11\noptions ndots:0\n"


def test_dynamic_mode_fails_closed_without_allowlist(tmp_path):
    result, calls, _ = _run_dynamic_firewall(tmp_path, hosts="")

    assert result.returncode == 1
    assert "requires FIREWALL_HOSTS" in result.stderr
    assert calls["dnsmasq"] == []


def test_dynamic_mode_fails_closed_without_ipv4_resolver(tmp_path):
    result, calls, resolv_conf = _run_dynamic_firewall(
        tmp_path,
        resolvers="nameserver 2001:db8::53\n",
    )

    assert result.returncode == 1
    assert "no usable IPv4 DNS resolver" in result.stderr
    assert calls["dnsmasq"] == []
    assert resolv_conf == "nameserver 2001:db8::53\n"
