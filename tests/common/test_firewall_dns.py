"""firewall.sh DNS hardening — retry dig before declaring a host unresolvable.

A single transient DNS miss on ANY allowlisted host used to abort the whole
agent container (observed: one empty dig answer for q.eu-central-1.amazonaws.com
killed a Copilot run before the agent started — a host that backend doesn't
even use). The script must retry dig a few times and only then hard-fail.
dig/iptables/sleep are stubbed on PATH, so no root or network is needed.

Run: uv run python -m pytest tests/common/test_firewall_dns.py -v
"""

import os
import stat
import subprocess

FIREWALL_SH = os.path.join(os.path.dirname(__file__), "..", "..", "docker", "firewall.sh")


def _stub(bindir, name, body):
    path = bindir / name
    path.write_text(f"#!/bin/bash\n{body}\n")
    path.chmod(path.stat().st_mode | stat.S_IEXEC)


def _run_firewall(tmp_path, fail_digs):
    """Run firewall.sh with stubbed tools: dig answers nothing for the first
    `fail_digs` calls, then resolves. Returns (proc, dig call count, iptables calls)."""
    bindir = tmp_path / "bin"
    bindir.mkdir()
    counter = tmp_path / "dig_calls"
    counter.write_text("0")
    iptables_calls = tmp_path / "iptables_calls"
    iptables_calls.write_text("")
    _stub(
        bindir,
        "dig",
        f'n=$(cat "{counter}"); n=$((n + 1)); echo "$n" > "{counter}"; '
        f'if [ "$n" -gt {fail_digs} ]; then echo 1.2.3.4; fi',
    )
    _stub(bindir, "iptables", f'printf "%s\\n" "$*" >> "{iptables_calls}"')
    _stub(bindir, "ip6tables", "exit 0")
    _stub(bindir, "sleep", "exit 0")  # keep the retry backoff instant
    env = {**os.environ, "PATH": f"{bindir}:{os.environ['PATH']}", "FIREWALL_HOSTS": "api.example.com"}
    proc = subprocess.run(["bash", FIREWALL_SH], capture_output=True, text=True, env=env, timeout=30)
    return proc, int(counter.read_text()), iptables_calls.read_text().splitlines()


def test_first_try_resolution_needs_no_retry(tmp_path):
    proc, dig_calls, _ = _run_firewall(tmp_path, fail_digs=0)
    assert proc.returncode == 0, proc.stderr
    assert dig_calls == 1
    assert "Allowed: api.example.com -> 1.2.3.4" in proc.stdout


def test_transient_dns_miss_is_retried(tmp_path):
    proc, dig_calls, _ = _run_firewall(tmp_path, fail_digs=2)
    assert proc.returncode == 0, proc.stderr
    assert dig_calls == 3
    assert "Allowed: api.example.com -> 1.2.3.4" in proc.stdout


def test_persistent_dns_failure_still_fails_after_retries(tmp_path):
    proc, dig_calls, _ = _run_firewall(tmp_path, fail_digs=99)
    assert proc.returncode == 1
    assert dig_calls == 3  # all retries spent before giving up
    assert "no IPs resolved for host 'api.example.com'" in proc.stderr


def test_https_accept_rule_is_scoped_to_resolved_ip(tmp_path):
    proc, _, iptables_calls = _run_firewall(tmp_path, fail_digs=0)

    assert proc.returncode == 0, proc.stderr
    https_accepts = [call for call in iptables_calls if "--dport 443" in call and "-j ACCEPT" in call]
    assert https_accepts == ["-A OUTPUT -d 1.2.3.4 -p tcp --dport 443 -j ACCEPT"]
    assert "-A OUTPUT -j DROP" in iptables_calls
