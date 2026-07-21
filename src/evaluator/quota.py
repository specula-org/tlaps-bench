"""Subscription usage measurement and the quota gate.

Two complementary mechanisms keep a run from being misgraded when a provider
limits the account:

- Proactive gate (``wait_for_quota``): before launching an agent, read the
  backend's subscription utilization (via its usage probe, see ``scripts/usage/``)
  and sleep until the window resets when it is over threshold.
- Reactive retry (``run_with_quota_retry``): after a run, if the backend reports
  a hard usage cap — the backend did no work (``Backend.detect_quota_block``) —
  sleep until the stated reset and retry rather than grade the no-op run as FAIL.

Both share ``secs_until_reset``, the single "how long until this resets" helper.
"""

from __future__ import annotations

import json
import math
import os
import subprocess
import time
from collections.abc import Callable
from datetime import datetime


def secs_until_reset(when, *, clamp_hi: int = 3600, buffer: int = 120, fallback: int = 600) -> int:
    """Seconds from now until ``when``, plus ``buffer``, clamped to [60, clamp_hi].

    ``when`` may be an ISO-8601 string, a ``datetime``, or ``None``; returns
    ``fallback`` when it is missing or unparseable. The upper clamp guards against
    a skewed system clock computing an absurd sleep (this host has shown corrupt
    process times); callers re-poll after sleeping, so a low clamp only costs an
    extra check, never a missed resume. The two call sites differ deliberately:
    the proactive gate caps at 1h (it re-reads usage cheaply), the reactive retry
    caps at 6h (the provider's stated reset is authoritative).
    """
    if when is None:
        return fallback
    try:
        dt = when if isinstance(when, datetime) else datetime.fromisoformat(when)
        secs = int(dt.timestamp() - time.time()) + buffer
        return min(max(secs, 60), clamp_hi)
    except Exception:
        return fallback


def fetch_usage(usage_script: str | None) -> dict | None:
    """Return the parsed usage JSON from a backend's probe, or None if unavailable.

    Fails open (returns None) on any error — missing script, no subscription/OAuth
    token, network failure, bad JSON. Callers treat None as "can't tell, proceed",
    so the gate never blocks a run it can't measure (e.g. the API-key path).
    """
    if not usage_script or not os.path.isfile(usage_script):
        return None
    try:
        r = subprocess.run(["bash", usage_script], capture_output=True, text=True, timeout=30)
    except Exception:
        return None
    if r.returncode != 0 or not r.stdout.strip():
        return None
    try:
        parsed = json.loads(r.stdout)
    except json.JSONDecodeError:
        return None
    return parsed if isinstance(parsed, dict) else None


def _usage_over(usage: dict, quota_5h: float, quota_7d: float):
    """Return (list of "5h=NN% (limit MM%)" strings, earliest resets_at) for any
    window over its limit. A limit <= 0 disables that window's check."""
    over = []
    resets = []
    for key, limit in (("five_hour", quota_5h), ("seven_day", quota_7d)):
        if limit <= 0:
            continue
        candidate = usage.get(key)
        obj = candidate if isinstance(candidate, dict) else {}
        raw_util = obj.get("utilization")
        if (isinstance(raw_util, int) and not isinstance(raw_util, bool)) or (
            isinstance(raw_util, float) and math.isfinite(raw_util)
        ):
            util = raw_util
        else:
            util = 0
        if util > limit:
            over.append(f"{key}={util}% (limit {limit}%)")
            ra = obj.get("resets_at")
            if isinstance(ra, str) and ra:
                resets.append(ra)
    earliest = sorted(resets)[0] if resets else None
    return over, earliest


def wait_for_quota(usage_script, quota_5h, quota_7d, max_waits, log_prefix: str = "") -> bool:
    """Block until subscription 5h/7d usage is under threshold.

    Polls ``usage_script``; if a window is over its limit, sleeps until that
    window's resets_at (+buffer), then re-checks. Returns True once under
    threshold (or when gating is disabled / usage can't be measured), or False
    after exceeding ``max_waits`` resets (caller should abort the benchmark).
    """
    if not usage_script or (quota_5h <= 0 and quota_7d <= 0):
        return True
    waits = 0
    while True:
        usage = fetch_usage(usage_script)
        if usage is None:
            return True  # fail open — can't measure, don't block
        over, reset_at = _usage_over(usage, quota_5h, quota_7d)
        if not over:
            return True
        waits += 1
        if waits > max_waits:
            print(
                f"{log_prefix}quota over after {max_waits} waits ({', '.join(over)}); aborting this benchmark",
                flush=True,
            )
            return False
        sleep_secs = secs_until_reset(reset_at, clamp_hi=3600)
        when = reset_at or f"+{sleep_secs}s"
        print(
            f"{log_prefix}quota over: {', '.join(over)} — sleeping "
            f"{sleep_secs}s until {when} (wait {waits}/{max_waits})",
            flush=True,
        )
        time.sleep(sleep_secs)


# Max times to sleep-through a hard provider usage cap for a single benchmark
# before giving up. Each sleep is the provider's stated reset, so a handful covers
# any real outage; the cap is just a runaway backstop.
MAX_QUOTA_RETRIES = 12


def run_with_quota_retry(
    run_once,
    detect_block,
    *,
    max_retries: int = MAX_QUOTA_RETRIES,
    log_prefix: str = "",
    prepare_retry: Callable[[int], bool] | None = None,
) -> bool:
    """Run the agent, sleeping through any hard provider usage-limit cap.

    The proactive gate (``wait_for_quota``) cannot see this cap: once hard-capped,
    the agent emits no usage events, so utilization reads stale and never trips,
    and every task would fail in ~3s and be misgraded FAIL. After each run we ask
    the backend (``detect_block``) whether the run hit the cap and how long to
    wait, then retry rather than grade a no-op run.

    ``run_once``: () -> None — launches the agent, writing its output.
    ``detect_block``: () -> int | None — seconds to wait, or None when no cap.
    ``prepare_retry``: (attempt_index) -> bool — optional hook called before a
    blocked attempt would be replaced. It can preserve telemetry and must return
    False when native evidence shows that retrying could duplicate paid work.
    Returns True if a run completed without hitting the cap, False if the cap
    persisted past ``max_retries`` or a retry was suppressed as unsafe.
    """
    for attempt in range(max_retries):
        run_once()
        block_secs = detect_block()
        if block_secs is None:
            return True
        if attempt == max_retries - 1:
            # Last attempt: the verdict is already "give up", so don't sleep
            # through a reset (up to 6h) we'll never use.
            break
        if prepare_retry is not None and not prepare_retry(attempt):
            print(
                f"{log_prefix}provider usage limit hit with possible prior model activity "
                "— not retrying potentially paid work",
                flush=True,
            )
            return False
        print(
            f"{log_prefix}provider usage limit hit — sleeping {block_secs}s then "
            f"retrying (attempt {attempt + 1}/{max_retries})",
            flush=True,
        )
        time.sleep(block_secs)
    return False
