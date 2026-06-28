"""scripts/usage/codex.sh — read codex rate limits from session rollouts.

It maps codex's local `rate_limits` snapshot (primary -> five_hour, secondary ->
seven_day, used_percent -> utilization) into the same JSON shape scripts/usage/
claude.sh emits, so the runner's quota gate consumes it unchanged. A window whose
resets_at is already in the past is reported as 0% (the snapshot's percent is stale).

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_codex_usage.py
"""

import json
import os
import subprocess

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SCRIPT = os.path.join(REPO_ROOT, "scripts", "usage", "codex.sh")

PAST = 1_000_000_000  # 2001 — always in the past
FUTURE = 4_102_444_800  # 2100 — always in the future


def _write_rollout(codex_home, primary, secondary):
    """Write one session rollout with a single token_count rate_limits event."""
    d = os.path.join(codex_home, "sessions", "2026", "06", "26")
    os.makedirs(d, exist_ok=True)
    event = {
        "timestamp": "2026-06-26T17:51:58.000Z",
        "type": "event_msg",
        "payload": {
            "type": "token_count",
            "info": {"total_token_usage": {"total_tokens": 1}},
            "rate_limits": {"primary": primary, "secondary": secondary},
        },
    }
    with open(os.path.join(d, "rollout-2026-06-26T17-51-58-abc.jsonl"), "w") as f:
        f.write(json.dumps(event) + "\n")


def _run(codex_home, *args):
    return subprocess.run(
        ["bash", SCRIPT, *args],
        capture_output=True,
        text=True,
        env={**os.environ, "CODEX_HOME": codex_home},
    )


def test_maps_windows_and_zeroes_stale(tmp_path):
    home = str(tmp_path / "codex")
    # primary already reset (stale 100%) -> reported 0; secondary live at 28%.
    _write_rollout(
        home,
        {"used_percent": 100.0, "window_minutes": 300, "resets_at": PAST},
        {"used_percent": 28.0, "window_minutes": 10080, "resets_at": FUTURE},
    )
    r = _run(home)
    assert r.returncode == 0, r.stderr
    out = json.loads(r.stdout)
    assert out["five_hour"]["utilization"] == 0  # stale window zeroed
    assert out["seven_day"]["utilization"] == 28.0  # live window preserved
    assert out["seven_day"]["resets_at"].startswith("2100-")  # epoch -> ISO


def test_check_mode_exit_codes(tmp_path):
    home = str(tmp_path / "codex")
    _write_rollout(
        home,
        {"used_percent": 10.0, "window_minutes": 300, "resets_at": FUTURE},
        {"used_percent": 28.0, "window_minutes": 10080, "resets_at": FUTURE},
    )
    assert _run(home, "--check", "95").returncode == 0  # both under
    over = _run(home, "--check", "20")  # 7d=28 > 20
    assert over.returncode == 1
    assert "7d=28" in over.stdout


def test_no_session_data_exits_2(tmp_path):
    home = str(tmp_path / "codex")
    os.makedirs(os.path.join(home, "sessions"), exist_ok=True)  # empty, no rollouts
    r = _run(home)
    assert r.returncode == 2  # runner treats this as "can't measure" -> fail open


def test_missing_used_percent_is_zero_not_crash(tmp_path):
    home = str(tmp_path / "codex")
    _write_rollout(
        home,
        {"window_minutes": 300, "resets_at": FUTURE},  # no used_percent
        {"used_percent": 5.0, "window_minutes": 10080, "resets_at": FUTURE},
    )
    out = json.loads(_run(home).stdout)
    assert out["five_hour"]["utilization"] == 0
    assert out["seven_day"]["utilization"] == 5.0


def test_window_without_reset_epoch_fails_open(tmp_path):
    # A high used_percent with no resets_at can't be checked for freshness and
    # gives the gate no recovery time, so it must report 0 (fail open), not block.
    home = str(tmp_path / "codex")
    _write_rollout(
        home,
        {"used_percent": 99.0, "window_minutes": 300},  # no resets_at
        {"used_percent": 5.0, "window_minutes": 10080, "resets_at": FUTURE},
    )
    out = json.loads(_run(home).stdout)
    assert out["five_hour"]["utilization"] == 0
    assert out["five_hour"]["resets_at"] is None
    assert out["seven_day"]["utilization"] == 5.0


def test_non_utf8_locale_does_not_crash(tmp_path):
    # Rollouts are real UTF-8 (serde_json). Under a non-UTF-8 host locale with
    # Python's UTF-8 mode off, `for line in f` would raise UnicodeDecodeError and
    # silently disable the gate unless the script decodes UTF-8 explicitly.
    home = str(tmp_path / "codex")
    d = os.path.join(home, "sessions", "2026", "06", "26")
    os.makedirs(d, exist_ok=True)
    event = {
        "type": "event_msg",
        "note": "café résumé déjà",  # multibyte UTF-8, written as raw bytes
        "payload": {
            "type": "token_count",
            "rate_limits": {
                "primary": {"used_percent": 12.0, "window_minutes": 300, "resets_at": FUTURE},
                "secondary": {"used_percent": 5.0, "window_minutes": 10080, "resets_at": FUTURE},
            },
        },
    }
    with open(os.path.join(d, "rollout-utf8.jsonl"), "w", encoding="utf-8") as f:
        f.write(json.dumps(event, ensure_ascii=False) + "\n")
    env = {**os.environ, "CODEX_HOME": home, "LC_ALL": "C", "LANG": "C", "PYTHONUTF8": "0"}
    r = subprocess.run(["bash", SCRIPT], capture_output=True, text=True, env=env)
    assert r.returncode == 0, r.stderr
    out = json.loads(r.stdout)
    assert out["five_hour"]["utilization"] == 12.0
