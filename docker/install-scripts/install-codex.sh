#!/bin/bash
set -e
npm install -g @openai/codex --cache /tmp/.npm && rm -rf /tmp/.npm

# Write auth.json from env vars if no auth file already present (e.g. from mounted copy)
if [ ! -f /root/.codex/auth.json ]; then
    mkdir -p /root/.codex
    if [ -n "${OPENAI_API_KEY:-}" ]; then
        printf '{"OPENAI_API_KEY": "%s"}\n' "$OPENAI_API_KEY" > /root/.codex/auth.json
    elif [ -n "${AZURE_OPENAI_API_KEY:-}" ]; then
        printf '{"AZURE_OPENAI_API_KEY": "%s", "AZURE_OPENAI_HOST": "%s"}\n' "$AZURE_OPENAI_API_KEY" "${AZURE_OPENAI_HOST:-}" > /root/.codex/auth.json
    fi
fi
