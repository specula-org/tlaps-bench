#!/usr/bin/env bash
# Restore a persisted agent session into a fresh container for debugging.
#
# Pair with `tlaps-bench run --session-dir <DIR>`, which writes each run's agent
# session state to <DIR>/<backend>/<benchmark>/ on the host. This script mounts
# one of those directories back into a new tlaps-bench-base container at the
# backend's session path and drops you into an interactive shell, so you can
# inspect the state or resume the agent CLI — even after the original container
# was removed or the host was rebooted.
#
# Usage:
#   scripts/restore-session.sh [--backend NAME] [--image IMG] <host-session-dir>
#
#   <host-session-dir>   e.g. <DIR>/copilot/my_benchmark  (the dir holding the
#                        agent's .copilot/.codex/.claude/.pi contents)
#   --backend NAME       copilot (default) | codex | claude_code | pi
#                        selects the in-container mount path
#   --image IMG          container image (default: tlaps-bench-base:latest)
#
# Example:
#   scripts/restore-session.sh --backend copilot ./sessions/copilot/my_benchmark
#   # then, inside the container:
#   copilot --resume        # or inspect ~/.copilot directly

set -euo pipefail

BACKEND="copilot"
IMAGE="tlaps-bench-base:latest"
SESSION_DIR=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --backend) BACKEND="${2:?--backend needs a value}"; shift 2 ;;
    --image) IMAGE="${2:?--image needs a value}"; shift 2 ;;
    -h|--help) sed -n '2,25p' "$0"; exit 0 ;;
    -*) echo "unknown option: $1" >&2; exit 2 ;;
    *) SESSION_DIR="$1"; shift ;;
  esac
done

if [[ -z "$SESSION_DIR" ]]; then
  echo "ERROR: missing <host-session-dir>. Run '$0 --help'." >&2
  exit 2
fi
if [[ ! -d "$SESSION_DIR" ]]; then
  echo "ERROR: not a directory: $SESSION_DIR" >&2
  exit 2
fi

# Map backend -> in-container session path (matches session_state_dir in
# src/evaluator/backends/*.py).
case "$BACKEND" in
  copilot) CONTAINER_PATH="/root/.copilot" ;;
  codex) CONTAINER_PATH="/root/.codex" ;;
  claude_code|claude) CONTAINER_PATH="/root/.claude" ;;
  pi) CONTAINER_PATH="/root/.pi" ;;
  *) echo "ERROR: unknown backend '$BACKEND' (copilot|codex|claude_code|pi)" >&2; exit 2 ;;
esac

SESSION_DIR="$(cd "$SESSION_DIR" && pwd)"
echo "Restoring $BACKEND session from $SESSION_DIR -> $CONTAINER_PATH in $IMAGE"
echo "(interactive shell; the container is removed on exit — the host session dir is not)"

exec docker run --rm -it \
  --platform linux/amd64 \
  -v "$SESSION_DIR:$CONTAINER_PATH:rw" \
  "$IMAGE" bash
