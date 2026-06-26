"""Scoring from results.json.

A task passes iff check_verdict == "PASS"; CHEATING/FAIL/TIMEOUT/ERROR all count
as not passed, and CHEATING is never shown as its own category. The default
"equal" scorer makes the score the plain percentage of tasks passed.

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_score.py
"""

import json

from evaluator.score import SCORERS, comparison_md, is_pass, load_run, scorecard_md, weighted_score

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
    run = {"path": "x/results.json", "id": "x", "backend": "codex", "level": "level1", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "CHEATING" not in md  # a cheat is folded into fail, never its own category
    assert "| A | 1 | 2 | 50.0% |" in md
    assert "| B | 1 | 1 | 100.0% |" in md
    assert "| **Total** | **2** | **3** | **66.7%** |" in md
    assert "**Pass rate**: 2/3 (66.7%)" in md


def test_comparison_row_per_run():
    runs = [
        {"id": "r1", "backend": "codex", "level": "level1", "results": [_r("PASS"), _r("FAIL")]},
        {"id": "r2", "backend": "claude_code", "level": "level1", "results": [_r("PASS"), _r("PASS")]},
    ]
    md = comparison_md(runs, EQUAL, "equal")
    assert "Comparison — 2 runs" in md
    assert "| r1 | codex | level1 | 50.0% | 1/2 |" in md
    assert "| r2 | claude_code | level1 | 100.0% | 2/2 |" in md


def test_load_run_from_dir(tmp_path):
    d = tmp_path / "run"
    d.mkdir()
    (d / "results.json").write_text(json.dumps([_r("PASS", backend="codex", level="level1")]))
    run = load_run(str(d))
    assert run["backend"] == "codex"
    assert run["level"] == "level1"
    assert len(run["results"]) == 1
