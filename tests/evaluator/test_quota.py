"""evaluator.quota — the shared usage/quota policy layer.

Covers secs_until_reset (the single "time until reset" helper that both the
proactive gate and the reactive hard-cap retry now share), the gate's fail-open
paths, and run_with_quota_retry's sleep-and-retry loop. The bash usage probes are
exercised separately (test_codex_usage.py); here we test the pure-Python policy.

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_quota.py
"""

from datetime import datetime, timedelta
from types import SimpleNamespace

from evaluator import quota


def test_secs_until_reset_future_iso_is_buffered_and_clamped():
    when = (datetime.now() + timedelta(minutes=10)).isoformat()
    secs = quota.secs_until_reset(when, clamp_hi=3600)
    assert 60 <= secs <= 3600
    assert 600 <= secs <= 800  # ~10min + 120s buffer, well under the 1h clamp


def test_secs_until_reset_accepts_datetime():
    secs = quota.secs_until_reset(datetime.now() + timedelta(hours=5), clamp_hi=6 * 3600)
    assert 60 <= secs <= 6 * 3600


def test_secs_until_reset_clamps_high():
    # a far-future reset is capped to clamp_hi, not a multi-day sleep
    assert quota.secs_until_reset(datetime.now() + timedelta(days=3), clamp_hi=3600) == 3600


def test_secs_until_reset_past_floors_to_60():
    assert quota.secs_until_reset((datetime.now() - timedelta(hours=1)).isoformat()) == 60


def test_secs_until_reset_none_and_garbage_fall_back():
    assert quota.secs_until_reset(None, fallback=1800) == 1800
    assert quota.secs_until_reset("not-a-time", fallback=600) == 600


def test_usage_over_flags_only_breached_windows():
    usage = {
        "five_hour": {"utilization": 90, "resets_at": "2030-01-01T00:00:00"},
        "seven_day": {"utilization": 50, "resets_at": "2030-01-02T00:00:00"},
    }
    over, earliest = quota._usage_over(usage, quota_5h=80, quota_7d=80)
    assert any("five_hour" in s for s in over)
    assert not any("seven_day" in s for s in over)
    assert earliest == "2030-01-01T00:00:00"


def test_usage_over_limit_zero_disables_window():
    usage = {"five_hour": {"utilization": 99}, "seven_day": {"utilization": 99}}
    over, earliest = quota._usage_over(usage, quota_5h=0, quota_7d=0)
    assert over == []
    assert earliest is None


def test_usage_over_ignores_malformed_window_fields():
    usage = {
        "five_hour": "not-an-object",
        "seven_day": {"utilization": "99", "resets_at": {"bad": "shape"}},
    }

    assert quota._usage_over(usage, quota_5h=80, quota_7d=80) == ([], None)


def test_wait_for_quota_disabled_returns_true():
    assert quota.wait_for_quota(None, 80, 95, 6) is True  # no probe -> gate off
    assert quota.wait_for_quota("scripts/usage/claude.sh", 0, 0, 6) is True  # both 0 -> off


def test_fetch_usage_missing_script_is_none():
    assert quota.fetch_usage(None) is None
    assert quota.fetch_usage("/no/such/script.sh") is None


def test_fetch_usage_rejects_valid_json_that_is_not_an_object(tmp_path, monkeypatch):
    script = tmp_path / "usage.sh"
    script.write_text("#!/bin/sh\n")
    monkeypatch.setattr(
        quota.subprocess,
        "run",
        lambda *args, **kwargs: SimpleNamespace(returncode=0, stdout="[1, 2, 3]"),
    )

    assert quota.fetch_usage(str(script)) is None


def test_run_with_quota_retry_no_cap_runs_once():
    calls = []
    ok = quota.run_with_quota_retry(lambda: calls.append(1), lambda: None)
    assert ok is True
    assert len(calls) == 1


def test_run_with_quota_retry_retries_then_succeeds(monkeypatch):
    monkeypatch.setattr(quota.time, "sleep", lambda s: None)
    calls = []
    blocks = [10, None]  # capped once, then clear
    ok = quota.run_with_quota_retry(lambda: calls.append(1), lambda: blocks.pop(0))
    assert ok is True
    assert len(calls) == 2


def test_run_with_quota_retry_stops_when_preparing_retry_finds_model_work(monkeypatch):
    slept = []
    monkeypatch.setattr(quota.time, "sleep", lambda seconds: slept.append(seconds))
    calls = []
    prepared = []

    ok = quota.run_with_quota_retry(
        lambda: calls.append(1),
        lambda: 10,
        prepare_retry=lambda attempt: prepared.append(attempt) or False,
    )

    assert ok is False
    assert len(calls) == 1
    assert prepared == [0]
    assert slept == []


def test_run_with_quota_retry_exhausts(monkeypatch):
    slept = []
    monkeypatch.setattr(quota.time, "sleep", lambda s: slept.append(s))
    calls = []
    ok = quota.run_with_quota_retry(lambda: calls.append(1), lambda: 10, max_retries=3)
    assert ok is False
    assert len(calls) == 3
    # last attempt must NOT sleep through a reset it will never use
    assert len(slept) == 2
