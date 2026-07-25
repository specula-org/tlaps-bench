#!/bin/bash
set -euo pipefail
# Cursor Agent CLI ships as a self-contained binary installed under
# $HOME/.local/bin. Symlink it onto the default PATH so the (non-login) agent
# shell can find `cursor-agent`. This runs before the firewall is applied, so
# the installer's downloads reach the internet freely.
curl https://cursor.com/install -fsS | bash
cursor_agent="$HOME/.local/bin/cursor-agent"
if [[ ! -x "$cursor_agent" ]]; then
    echo "Cursor installer did not create executable: $cursor_agent" >&2
    exit 1
fi
ln -sf "$cursor_agent" /usr/local/bin/cursor-agent
