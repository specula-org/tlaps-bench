#!/bin/bash
set -e

# ============================================================
# Network firewall: whitelist-only outbound access.
# Allows DNS + OpenAI / Azure OpenAI / Anthropic inference APIs only;
# github.com and api.github.com (repos/web) are blocked to prevent
# data leakage/cheating.
#
# Exception: the copilot backend. The Copilot CLI must reach api.github.com
# (OAuth token exchange + user validation) and inference hosts behind a
# rotating CDN that IP-whitelisting cannot reliably allow, so the firewall is
# skipped for copilot runs. Set DISABLE_FIREWALL=1 to force-skip it for any
# backend.
# ============================================================
case " $* " in
    *"--backend copilot"*|*" copilot "*) DISABLE_FIREWALL="${DISABLE_FIREWALL:-1}" ;;
esac

if [ "${DISABLE_FIREWALL:-0}" = "1" ]; then
    echo "[entrypoint] ============================================================"
    echo "[entrypoint] WARNING: outbound network firewall is DISABLED for this run."
    echo "[entrypoint] The copilot backend needs api.github.com (token exchange/"
    echo "[entrypoint] validation) plus CDN-rotating inference hosts, which an IP"
    echo "[entrypoint] whitelist cannot reliably allow, so outbound network is left"
    echo "[entrypoint] UNRESTRICTED."
    echo "[entrypoint] ============================================================"
else
    # Allow loopback
    iptables -A OUTPUT -o lo -j ACCEPT

    # Allow established connections (replies to our requests)
    iptables -A OUTPUT -m state --state ESTABLISHED,RELATED -j ACCEPT

    # Allow DNS (needed to resolve API hostnames)
    iptables -A OUTPUT -p udp --dport 53 -j ACCEPT
    iptables -A OUTPUT -p tcp --dport 53 -j ACCEPT

    # Whitelist inference API domains by resolving their IPs.
    API_HOSTS="api.openai.com api.anthropic.com"

    # Azure OpenAI (if AZURE_OPENAI_HOST is set)
    if [ -n "${AZURE_OPENAI_HOST:-}" ]; then
        API_HOSTS="$API_HOSTS $AZURE_OPENAI_HOST"
    fi

    for host in $API_HOSTS; do
        for ip in $(dig +short "$host" 2>/dev/null | grep -E '^[0-9]'); do
            iptables -A OUTPUT -d "$ip" -p tcp --dport 443 -j ACCEPT
            echo "[entrypoint] Allowed: $host -> $ip"
        done
    done

    # Drop everything else
    iptables -A OUTPUT -j DROP

    echo "[entrypoint] Firewall configured: only API endpoints allowed, all other traffic blocked"
fi

# Fix bench user UID/GID to match host (avoids permission issues on mounted volumes)
HOST_UID="${HOST_UID:-1000}"
HOST_GID="${HOST_GID:-1000}"
CURRENT_UID=$(id -u bench)
CURRENT_GID=$(id -g bench)
if [ "$CURRENT_UID" != "$HOST_UID" ] || [ "$CURRENT_GID" != "$HOST_GID" ]; then
    groupmod -g "$HOST_GID" bench 2>/dev/null || true
    usermod -u "$HOST_UID" -g "$HOST_GID" bench 2>/dev/null || true
    chown -R bench:bench /home/bench
fi

# Fix ownership of mounted config files for bench user
if [ -f /mnt/codex-config.toml ]; then
    mkdir -p /home/bench/.codex
    cp /mnt/codex-config.toml /home/bench/.codex/config.toml
    chown -R bench:bench /home/bench/.codex
fi

# GitHub Copilot CLI config (copilot backend): if mounted, install it so the
# CLI picks up the stored OAuth token / PAT without setting an env var. This
# mirrors the codex-config mount above. Use either this OR
# COPILOT_GITHUB_TOKEN — not both needed.
if [ -f /mnt/copilot-config.json ]; then
    mkdir -p /home/bench/.copilot
    cp /mnt/copilot-config.json /home/bench/.copilot/config.json
    chown -R bench:bench /home/bench/.copilot
fi

# Drop privileges and exec the command as bench user
exec gosu bench "$@"
