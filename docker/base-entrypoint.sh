#!/bin/bash
# Base entrypoint for tlaps-bench agent containers.
# Runs firewall setup, then execs the provided command.
set -e

# Run firewall (needs CAP_NET_ADMIN)
/opt/firewall.sh 2>/dev/null || true

exec "$@"
