#!/bin/bash
set -e

# ============================================================
# Network firewall: whitelist-only outbound access
# Only allow DNS + OpenAI / Azure OpenAI / Anthropic / GitHub Copilot
# *inference* APIs. Everything else — including github.com and
# api.github.com (repos/web) — is blocked to prevent data leakage/cheating.
# ============================================================

# Allow loopback
iptables -A OUTPUT -o lo -j ACCEPT

# Allow established connections (replies to our requests)
iptables -A OUTPUT -m state --state ESTABLISHED,RELATED -j ACCEPT

# Allow DNS (needed to resolve API hostnames)
iptables -A OUTPUT -p udp --dport 53 -j ACCEPT
iptables -A OUTPUT -p tcp --dport 53 -j ACCEPT

# Whitelist API domains by resolving their IPs
# OpenAI API (codex backend) + Anthropic API (claude_code backend)
#   + GitHub Copilot inference API (copilot backend).
# NB: only the *inference* hosts are whitelisted — github.com and
# api.github.com are intentionally NOT allowed, so the agent cannot reach
# GitHub repos/web (anti-cheating). The Copilot host varies by plan, so all
# three are listed; the copilot backend runs --no-auto-update so it never
# needs api.github.com for a release check.
API_HOSTS="api.openai.com api.anthropic.com api.githubcopilot.com api.business.githubcopilot.com api.enterprise.githubcopilot.com"

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
