#!/bin/bash
# Firewall script for tlaps-bench agent containers.
# Whitelists only specified API hosts; blocks all other outbound traffic.
# Reads FIREWALL_HOSTS env var (comma-separated hostnames).
# Set DISABLE_FIREWALL=1 to skip entirely.
set -e

if [ "${DISABLE_FIREWALL:-0}" = "1" ]; then
    exit 0
fi

if [ -z "${FIREWALL_HOSTS:-}" ]; then
    if [ "${DYNAMIC_FIREWALL:-0}" = "1" ]; then
        echo "[firewall] ERROR: dynamic firewall requires FIREWALL_HOSTS" >&2
        exit 1
    fi
    echo "[firewall] No FIREWALL_HOSTS set, skipping firewall"
    exit 0
fi

if [ "${DYNAMIC_FIREWALL:-0}" = "1" ]; then
    DNSMASQ_USER="tlaps-dnsmasq"
    DNSMASQ_UID=$(id -u "$DNSMASQ_USER")
    DNSMASQ_IPSET="tlaps-egress-v4"
    RESOLV_CONF="${RESOLV_CONF:-/etc/resolv.conf}"

    is_ipv4() {
        local address="$1"
        local octet
        local -a octets
        [[ "$address" =~ ^([0-9]{1,3}\.){3}[0-9]{1,3}$ ]] || return 1
        IFS='.' read -ra octets <<< "$address"
        for octet in "${octets[@]}"; do
            ((10#"$octet" <= 255)) || return 1
        done
        return 0
    }

    DOCKER_DNS_SERVERS=()
    while read -r directive resolver _ || [ -n "${directive:-}" ]; do
        if [ "$directive" != "nameserver" ] || ! is_ipv4 "$resolver" || [ "$resolver" = "127.0.0.1" ]; then
            continue
        fi
        if [[ ! " ${DOCKER_DNS_SERVERS[*]} " =~ " ${resolver} " ]]; then
            DOCKER_DNS_SERVERS+=("$resolver")
        fi
    done < "$RESOLV_CONF"

    if [ "${#DOCKER_DNS_SERVERS[@]}" -eq 0 ]; then
        echo "[firewall] ERROR: no usable IPv4 DNS resolver in $RESOLV_CONF" >&2
        exit 1
    fi

    DNSMASQ_ARGS=(
        --conf-file=
        --no-resolv
        --no-hosts
        --bind-interfaces
        --listen-address=127.0.0.1
        --port=53
        --user="$DNSMASQ_USER"
        --group="$DNSMASQ_USER"
        --pid-file=/run/tlaps-dnsmasq.pid
        --stop-dns-rebind
        --filter-AAAA
        --address=/#/
    )

    IFS=',' read -ra HOSTS <<< "$FIREWALL_HOSTS"
    for host in "${HOSTS[@]}"; do
        host=$(echo "$host" | xargs)
        host="${host,,}"
        if [[ "$host" == \*.* ]]; then
            host="${host#*.}"
        fi
        if [ "${#host}" -gt 253 ] || [[ ! "$host" =~ ^([a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?\.)+[a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?$ ]]; then
            echo "[firewall] ERROR: invalid dynamic firewall hostname '$host'" >&2
            exit 1
        fi
        for resolver in "${DOCKER_DNS_SERVERS[@]}"; do
            DNSMASQ_ARGS+=("--server=/${host}/${resolver}")
        done
        DNSMASQ_ARGS+=("--ipset=/${host}/${DNSMASQ_IPSET}")
    done

    ipset -exist create "$DNSMASQ_IPSET" hash:ip family inet maxelem 65536

    # Only the dedicated dnsmasq UID may reach the upstream resolvers.
    # Agent DNS is restricted to the local dnsmasq listener; these DNS-specific
    # rules precede the general loopback allow rule so upstream DNS is not exposed.
    for resolver in "${DOCKER_DNS_SERVERS[@]}"; do
        iptables -A OUTPUT -p udp -d "$resolver" --dport 53 \
            -m owner --uid-owner "$DNSMASQ_UID" -j ACCEPT
        iptables -A OUTPUT -p tcp -d "$resolver" --dport 53 \
            -m owner --uid-owner "$DNSMASQ_UID" -j ACCEPT
    done
    iptables -A OUTPUT -p udp -d 127.0.0.1 --dport 53 -j ACCEPT
    iptables -A OUTPUT -p tcp -d 127.0.0.1 --dport 53 -j ACCEPT
    iptables -A OUTPUT -p udp --dport 53 -j DROP
    iptables -A OUTPUT -p tcp --dport 53 -j DROP

    # Never trust an ipset entry for a private, shared, link-local, benchmark,
    # multicast, or reserved destination. These rules also protect against a
    # resolver regression or an address inserted before rebinding checks.
    for blocked_net in \
        0.0.0.0/8 \
        10.0.0.0/8 \
        100.64.0.0/10 \
        169.254.0.0/16 \
        172.16.0.0/12 \
        192.0.0.0/24 \
        192.0.2.0/24 \
        192.88.99.0/24 \
        192.168.0.0/16 \
        198.18.0.0/15 \
        198.51.100.0/24 \
        203.0.113.0/24 \
        224.0.0.0/4 \
        240.0.0.0/4
    do
        iptables -A OUTPUT -d "$blocked_net" -j DROP
    done

    iptables -A OUTPUT -o lo -j ACCEPT
    iptables -A OUTPUT -m set --match-set "$DNSMASQ_IPSET" dst \
        -p tcp --dport 443 -j ACCEPT
    iptables -A OUTPUT -j DROP
    ip6tables -P OUTPUT DROP

    dnsmasq "${DNSMASQ_ARGS[@]}"
    printf 'nameserver 127.0.0.1\noptions ndots:0\n' > "$RESOLV_CONF"
    echo "[firewall] Dynamic mode active: only ${FIREWALL_HOSTS} allowed"
    exit 0
fi

# Allow loopback
iptables -A OUTPUT -o lo -j ACCEPT

# Allow established connections
iptables -A OUTPUT -m state --state ESTABLISHED,RELATED -j ACCEPT

# Allow DNS
iptables -A OUTPUT -p udp --dport 53 -j ACCEPT
iptables -A OUTPUT -p tcp --dport 53 -j ACCEPT

# Whitelist API hosts
IFS=',' read -ra HOSTS <<< "$FIREWALL_HOSTS"
for host in "${HOSTS[@]}"; do
    host=$(echo "$host" | xargs)  # trim whitespace
    HOST_COUNT=0
    # Retry transient DNS misses — one empty dig answer for a single host must
    # not abort the whole container.
    for dns_attempt in 1 2 3; do
        for ip in $(dig +short "$host" 2>/dev/null | grep -E '^[0-9]'); do
            iptables -A OUTPUT -d "$ip" -p tcp --dport 443 -j ACCEPT
            echo "[firewall] Allowed: $host -> $ip"
            HOST_COUNT=$((HOST_COUNT + 1))
        done
        if [ "$HOST_COUNT" -gt 0 ]; then
            break
        fi
        if [ "$dns_attempt" -lt 3 ]; then
            sleep 2
        fi
    done
    if [ "$HOST_COUNT" -eq 0 ]; then
        echo "[firewall] ERROR: no IPs resolved for host '$host'" >&2
        exit 1
    fi
done

# Block all IPv6
ip6tables -P OUTPUT DROP 2>/dev/null || true

# Drop everything else
iptables -A OUTPUT -j DROP
echo "[firewall] Active: only ${FIREWALL_HOSTS} allowed"
