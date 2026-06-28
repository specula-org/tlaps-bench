"""CodexBackend.detect_quota_block — recognise ChatGPT's hard usage cap.

The percentage quota gate is blind to the hard cap: once rate-limited, codex's
turns fail instantly with no usage event, so the rolling utilization the gate
reads goes stale and never trips. The runner instead asks the backend, after each
agent run, whether the run hit the cap (via the agent's own `error`/`turn.failed`
events) and sleeps until the stated reset rather than grading a no-op run as FAIL.

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_codex_quota_block.py
"""

import json
import os

from evaluator.backends.codex import CodexBackend

# The exact event stream codex emits when the account is capped.
USAGE_LIMIT_STREAM = [
    {"type": "thread.started", "thread_id": "t1"},
    {"type": "turn.started"},
    {"type": "error", "message": "You've hit your usage limit. Visit https://chatgpt.com/codex/settings/usage to purchase more credits or try again at 7:24 PM."},
    {"type": "turn.failed", "error": {"message": "You've hit your usage limit. ... try again at 7:24 PM."}},
]

NORMAL_STREAM = [
    {"type": "thread.started", "thread_id": "t2"},
    {"type": "turn.started"},
    {"type": "item.completed", "item": {"id": "i0", "type": "agent_message", "text": "done"}},
    {"type": "turn.completed", "usage": {"input_tokens": 100, "output_tokens": 10}},
]


def _write_jsonl(path, events):
    with open(path, "w") as f:
        for e in events:
            f.write(json.dumps(e) + "\n")


def _write_rollout(codex_home, primary, secondary):
    """Write one codex session rollout carrying a rate_limits snapshot."""
    d = os.path.join(codex_home, "sessions", "2026", "06", "26")
    os.makedirs(d, exist_ok=True)
    event = {
        "type": "event_msg",
        "payload": {"type": "token_count", "rate_limits": {"primary": primary, "secondary": secondary}},
    }
    with open(os.path.join(d, "rollout-2026-06-26T17-51-58-abc.jsonl"), "w") as f:
        f.write(json.dumps(event) + "\n")


def test_usage_limit_blocks(tmp_path, monkeypatch):
    # No session data -> probe returns None -> falls back to parsing the prose time.
    monkeypatch.setenv("CODEX_HOME", str(tmp_path / "empty"))
    p = os.path.join(tmp_path, "out.jsonl")
    _write_jsonl(p, USAGE_LIMIT_STREAM)
    secs = CodexBackend().detect_quota_block(p)
    assert isinstance(secs, int)
    assert 60 <= secs <= 6 * 3600


def test_prefers_probe_reset_over_prose(tmp_path, monkeypatch):
    # The probe's precise 5h reset epoch (~2h out) must win over the prose
    # "try again at 7:24 PM" in the message — solving the tz/boundary fragility.
    import time

    home = str(tmp_path / "codex")
    future = int(time.time()) + 2 * 3600
    _write_rollout(
        home,
        {"used_percent": 100.0, "window_minutes": 300, "resets_at": future},
        {"used_percent": 5.0, "window_minutes": 10080, "resets_at": future + 999},
    )
    monkeypatch.setenv("CODEX_HOME", home)
    p = os.path.join(tmp_path, "out.jsonl")
    _write_jsonl(p, USAGE_LIMIT_STREAM)
    secs = CodexBackend().detect_quota_block(p)
    assert 2 * 3600 - 300 <= secs <= 2 * 3600 + 300  # tracks the probe, not the prose


def test_normal_run_does_not_block(tmp_path):
    p = os.path.join(tmp_path, "out.jsonl")
    _write_jsonl(p, NORMAL_STREAM)
    assert CodexBackend().detect_quota_block(p) is None


def test_missing_file_does_not_block(tmp_path):
    assert CodexBackend().detect_quota_block(os.path.join(tmp_path, "nope.jsonl")) is None


def test_parse_retry_time_returns_future_datetime():
    from datetime import datetime

    b = CodexBackend()
    # any AM/PM clock time parses to a today-or-tomorrow datetime (never past);
    # the seconds clamp lives in quota.secs_until_reset (see test_quota.py).
    for s in (
        "try again at 11:30 AM.",
        "try again at 7:24 PM.",
        "try again at 12:00 AM.",  # 12-hour edge cases must not raise
        "try again at 12:00 PM.",
    ):
        dt = b._parse_retry_time(s)
        assert isinstance(dt, datetime)
        assert dt >= datetime.now()


def test_unparseable_time_returns_none():
    assert CodexBackend()._parse_retry_time("usage limit, no reset time") is None
