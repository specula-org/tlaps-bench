"""Scoring from results.json.

A task passes iff check_verdict == "PASS"; CHEATING/FAIL/TIMEOUT/ERROR all count
as not passed, and CHEATING is never shown as its own category. The default
"equal" scorer makes the score the plain percentage of tasks passed. SKIP is the
one exception: it is dropped from scoring entirely (neither passed nor failed)
and only reported as a side count.

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_score.py
"""

import json
import sys

from evaluator.score import (
    SCORERS,
    comparison_md,
    is_pass,
    is_skipped,
    load_run,
    main,
    n_skipped,
    scorecard_md,
    weighted_score,
)

EQUAL = SCORERS["equal"]


def _r(verdict, module="M", **kw):
    d = {"check_verdict": verdict, "module": module, "input_tokens": 0, "output_tokens": 0, "time_secs": 0}
    d.update(kw)
    return d


def test_is_pass_only_for_PASS():
    assert is_pass(_r("PASS"))
    for v in ["FAIL", "CHEATING", "TIMEOUT", "ERROR"]:
        assert not is_pass(_r(v))


def test_cheating_counts_as_fail():
    results = [_r("PASS"), _r("PASS"), _r("CHEATING"), _r("FAIL")]
    pct, n_pass, n_total = weighted_score(results, EQUAL)
    assert (n_pass, n_total) == (2, 4)
    assert pct == 50.0


def test_equal_weight_is_percent_passed():
    results = [_r("PASS")] * 3 + [_r("FAIL")]
    pct, n_pass, n_total = weighted_score(results, EQUAL)
    assert (n_pass, n_total, pct) == (3, 4, 75.0)


def test_empty_is_zero_not_crash():
    assert weighted_score([], EQUAL) == (0.0, 0, 0)


def test_scorecard_module_breakdown_and_no_cheating_row():
    results = [_r("PASS", module="A"), _r("CHEATING", module="A"), _r("PASS", module="B")]
    run = {"path": "x/results.json", "id": "x", "backend": "codex", "mode": "auto-complete", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "CHEATING" not in md  # a cheat is folded into fail, never its own category
    assert "| A | 1 | 2 | 50.0% |" in md
    assert "| B | 1 | 1 | 100.0% |" in md
    assert "| **Total** | **2** | **3** | **66.7%** |" in md
    assert "**Pass rate**: 2/3 (66.7%)" in md


def test_comparison_row_per_run():
    runs = [
        {"id": "r1", "backend": "codex", "mode": "auto-complete", "results": [_r("PASS"), _r("FAIL")]},
        {"id": "r2", "backend": "claude_code", "mode": "auto-complete", "results": [_r("PASS"), _r("PASS")]},
    ]
    md = comparison_md(runs, EQUAL, "equal")
    assert "Comparison — 2 runs" in md
    assert "| r1 | codex | auto-complete | 50.0% | 1/2 |" in md
    assert "| r2 | claude_code | auto-complete | 100.0% | 2/2 |" in md


def test_load_run_from_dir(tmp_path):
    d = tmp_path / "run"
    d.mkdir()
    (d / "results.json").write_text(json.dumps([_r("PASS", backend="codex", mode="auto-complete")]))
    run = load_run(str(d))
    assert run["backend"] == "codex"
    assert run["mode"] == "auto-complete"
    assert len(run["results"]) == 1


# --- SKIP is excluded from scoring, not counted as a failure --------------


def test_is_skipped_only_for_SKIP():
    assert is_skipped(_r("SKIP"))
    for v in ["PASS", "FAIL", "CHEATING", "TIMEOUT", "ERROR"]:
        assert not is_skipped(_r(v))


def test_skip_drops_out_of_denominator():
    # 1 PASS + 1 FAIL + 1 SKIP -> 1/2 (50%), NOT 1/3: the skip is excluded.
    results = [_r("PASS"), _r("FAIL"), _r("SKIP")]
    pct, n_pass, n_total = weighted_score(results, EQUAL)
    assert (n_pass, n_total, pct) == (1, 2, 50.0)
    assert n_skipped(results) == 1


def test_all_skip_is_zero_not_crash():
    results = [_r("SKIP"), _r("SKIP")]
    assert weighted_score(results, EQUAL) == (0.0, 0, 0)
    assert n_skipped(results) == 2


def test_scorecard_excludes_skip_and_reports_it():
    # Module A: PASS + SKIP -> 1/1 (skip gone). Module B: all SKIP -> absent.
    results = [_r("PASS", module="A"), _r("SKIP", module="A"), _r("SKIP", module="B")]
    run = {"path": "x/results.json", "id": "x", "backend": "codex", "mode": "auto-complete", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "**Pass rate**: 1/1 (100.0%) · 2 skipped" in md
    assert "| A | 1 | 1 | 100.0% |" in md  # skip not counted against module A
    assert "| B |" not in md  # a fully-skipped module drops out of the table
    assert "| **Total** | **1** | **1** | **100.0%** |" in md


def test_scorecard_no_skip_has_no_skipped_note():
    results = [_r("PASS"), _r("FAIL")]
    run = {"path": "x/results.json", "id": "x", "backend": "codex", "mode": "auto-complete", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "**Pass rate**: 1/2 (50.0%)" in md
    assert "skipped" not in md


def test_comparison_discloses_skip_inline():
    runs = [
        {"id": "r1", "backend": "codex", "mode": "auto-complete", "results": [_r("PASS"), _r("FAIL"), _r("SKIP")]},
        {"id": "r2", "backend": "claude_code", "mode": "auto-complete", "results": [_r("PASS"), _r("PASS")]},
    ]
    md = comparison_md(runs, EQUAL, "equal")
    assert "| r1 | codex | auto-complete | 50.0% | 1/2 (+1 skipped) |" in md
    assert "| r2 | claude_code | auto-complete | 100.0% | 2/2 |" in md  # no note when nothing skipped


# --- load_run / main entry point ------------------------------------------


def test_load_run_from_file_path(tmp_path):
    f = tmp_path / "results.json"
    f.write_text(json.dumps([_r("PASS", backend="codex", mode="auto-complete")]))
    run = load_run(str(f))
    assert run["path"] == str(f)
    assert run["backend"] == "codex"
    assert run["id"] == tmp_path.name  # id falls back to the containing dir


def _write_run(tmp_path, name, results):
    d = tmp_path / name
    d.mkdir()
    (d / "results.json").write_text(json.dumps(results))
    return str(d)


def test_main_single_prints_scorecard(tmp_path, monkeypatch, capsys):
    d = _write_run(tmp_path, "run1", [_r("PASS", backend="codex", mode="auto-complete"), _r("FAIL")])
    monkeypatch.setattr(sys, "argv", ["tlaps-bench score", d])
    assert main() == 0
    out = capsys.readouterr().out
    assert "# Scorecard" in out
    assert "**Pass rate**: 1/2 (50.0%)" in out


def test_main_multiple_prints_comparison(tmp_path, monkeypatch, capsys):
    d1 = _write_run(tmp_path, "run1", [_r("PASS", backend="codex", mode="auto-complete")])
    d2 = _write_run(tmp_path, "run2", [_r("FAIL", backend="codex", mode="auto-complete")])
    monkeypatch.setattr(sys, "argv", ["tlaps-bench score", d1, d2])
    assert main() == 0
    assert "# Comparison — 2 runs" in capsys.readouterr().out


def test_main_missing_path_exits_1(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(sys, "argv", ["tlaps-bench score", str(tmp_path / "nope")])
    assert main() == 1
    assert "no results.json" in capsys.readouterr().err
