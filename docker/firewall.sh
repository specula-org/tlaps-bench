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
    echo "[firewall] No FIREWALL_HOSTS set, skipping firewall"
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
    for ip in $(dig +short "$host" 2>/dev/null | grep -E '^[0-9]'); do
        iptables -A OUTPUT -d "$ip" -p tcp --dport 443 -j ACCEPT
        echo "[firewall] Allowed: $host -> $ip"
        HOST_COUNT=$((HOST_COUNT + 1))
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
