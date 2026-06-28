#!/usr/bin/env bash
#
# Read Codex (ChatGPT) subscription usage from the local session rollouts.
#
# Codex records account-wide rate-limit snapshots in its session rollout files
# ($CODEX_HOME/sessions/YYYY/MM/DD/rollout-*.jsonl) as `token_count` events
# whose payload carries a `rate_limits` object:
#   primary   -> 5-hour window (window_minutes 300)
#   secondary -> weekly window (window_minutes 10080)
# each with `used_percent` and `resets_at` (unix epoch seconds).
#
# This emits the SAME JSON shape as scripts/usage/claude.sh, so the benchmark
# runner's quota gate (src/evaluator/runner.py) consumes it unchanged:
#   {"five_hour": {"utilization": N, "resets_at": "ISO"},
#    "seven_day": {"utilization": N, "resets_at": "ISO"}}
# mapping primary -> five_hour, secondary -> seven_day, used_percent -> utilization.
#
# A window whose resets_at is already in the past has rolled over since the
# snapshot was written, so its used_percent is stale: we report 0 for it rather
# than block on an expired number.
#
# Usage:
#   bash scripts/usage/codex.sh              # JSON (same shape as claude.sh)
#   bash scripts/usage/codex.sh --check 95   # exit 1 if 5h/7d window > 95%
#   bash scripts/usage/codex.sh --summary    # one human-readable line per window
#
# Override the codex home with CODEX_HOME (default $HOME/.codex).
#
# Exit codes:
#   0  ok (or under threshold in --check mode)
#   1  over threshold (--check mode)
#   2  no usage data (no session rollout with rate_limits found)

set -euo pipefail

export CODEX_HOME="${CODEX_HOME:-$HOME/.codex}"
export USAGE_MODE="${1:-}"
export USAGE_THRESHOLD="${2:-95}"

python3 <<'PY'
import glob
import json
import os
import sys
from datetime import datetime, timezone

home = os.environ["CODEX_HOME"]
mode = os.environ.get("USAGE_MODE", "")
sessions = os.path.join(home, "sessions")


def find_rate_limits(obj):
    """Depth-first search for a `rate_limits` dict anywhere in an event."""
    if isinstance(obj, dict):
        rl = obj.get("rate_limits")
        if isinstance(rl, dict):
            return rl
        for v in obj.values():
            r = find_rate_limits(v)
            if r:
                return r
    elif isinstance(obj, list):
        for v in obj:
            r = find_rate_limits(v)
            if r:
                return r
    return None


def last_rate_limits(path):
    """The last rate_limits snapshot in one rollout file, or None."""
    found = None
    try:
        # Rollouts are UTF-8 (serde_json); decode explicitly so a non-UTF-8 host
        # locale doesn't raise UnicodeDecodeError on `for line in f` and silently
        # disable the gate. errors="replace" keeps a stray byte from crashing us.
        with open(path, encoding="utf-8", errors="replace") as f:
            for line in f:
                if '"rate_limits"' not in line:
                    continue
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                rl = find_rate_limits(event)
                if rl:
                    found = rl
    except (OSError, ValueError):
        return None
    return found


# Newest-written rollout first; the freshest snapshot lives in the session
# codex touched most recently. Scan a few in case the very newest session
# crashed before emitting any token_count event.
files = glob.glob(os.path.join(sessions, "**", "rollout-*.jsonl"), recursive=True)
files.sort(key=os.path.getmtime, reverse=True)

rate_limits = None
for path in files[:10]:
    rate_limits = last_rate_limits(path)
    if rate_limits:
        break

if not rate_limits:
    sys.stderr.write(f"error: no codex session usage data under {sessions}\n")
    sys.exit(2)

now = datetime.now(timezone.utc).timestamp()


def window(obj):
    obj = obj or {}
    used = obj.get("used_percent")
    resets = obj.get("resets_at")
    iso = None
    if isinstance(resets, (int, float)):
        iso = datetime.fromtimestamp(resets, tz=timezone.utc).isoformat()
        if resets <= now:
            used = 0  # window already rolled over; the snapshot's percent is stale
    else:
        # No usable reset epoch — we can't tell whether used_percent is fresh and
        # the gate would have no resets_at to sleep until, so fail open (report 0)
        # rather than block on a possibly-stale value with no recovery time.
        used = 0
    return {"utilization": used if used is not None else 0, "resets_at": iso}


out = {
    "five_hour": window(rate_limits.get("primary")),
    "seven_day": window(rate_limits.get("secondary")),
}

if mode == "--check":
    threshold = float(os.environ.get("USAGE_THRESHOLD", "95"))
    over = []
    for name, key in (("5h", "five_hour"), ("7d", "seven_day")):
        util = out[key].get("utilization") or 0
        if util > threshold:
            over.append(f"{name}={util}% resets_at={out[key].get('resets_at') or ''}")
    if over:
        print("\n".join(over))
        sys.exit(1)
    print("ok")
elif mode == "--summary":
    for name, key in (("5h ", "five_hour"), ("7d ", "seven_day")):
        o = out[key]
        print(f"{name}\t{o.get('utilization'):>5}%   resets_at={o.get('resets_at') or '-'}")
else:
    print(json.dumps(out))
PY
