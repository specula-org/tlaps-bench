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
    continuation_budget,
    continuation_interrupted,
    continuation_passed,
    is_pass,
    is_pass_with_continuations,
    is_skipped,
    load_run,
    main,
    n_non_genuine,
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
    run = {"path": "x/results.json", "id": "x", "backend": "codex", "mode": "proof-completion", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "CHEATING" not in md  # a cheat is folded into fail, never its own category
    assert "| A | 1 | 2 | 50.0% |" in md
    assert "| B | 1 | 1 | 100.0% |" in md
    assert "| **Total** | **2** | **3** | **66.7%** |" in md
    assert "**Pass rate**: 2/3 (66.7%)" in md


def test_comparison_row_per_run():
    runs = [
        {"id": "r1", "backend": "codex", "mode": "proof-completion", "results": [_r("PASS"), _r("FAIL")]},
        {"id": "r2", "backend": "claude_code", "mode": "proof-completion", "results": [_r("PASS"), _r("PASS")]},
    ]
    md = comparison_md(runs, EQUAL, "equal")
    assert "Comparison — 2 runs" in md
    assert "| r1 | codex | proof-completion | 50.0% | 1/2 |" in md
    assert "| r2 | claude_code | proof-completion | 100.0% | 2/2 |" in md


def test_load_run_from_dir(tmp_path):
    d = tmp_path / "run"
    d.mkdir()
    (d / "results.json").write_text(json.dumps([_r("PASS", backend="codex", mode="proof-completion")]))
    run = load_run(str(d))
    assert run["backend"] == "codex"
    assert run["mode"] == "proof-completion"
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


def test_non_genuine_terminations_are_excluded_either_verdict():
    # A startup failure can leave a no-op workspace that grades PASS on a
    # defective task. INFRA_ERROR / QUOTA_EXHAUSTED results must count neither
    # as passes nor failures; they need a rerun.
    results = [
        _r("PASS"),
        _r("FAIL"),
        _r("PASS", termination_reason="INFRA_ERROR"),
        _r("FAIL", termination_reason="INFRA_ERROR"),
        _r("ERROR", termination_reason="QUOTA_EXHAUSTED"),
    ]
    pct, n_pass, n_total = weighted_score(results, EQUAL)
    assert (n_pass, n_total, pct) == (1, 2, 50.0)
    assert n_non_genuine(results) == 3


def test_ok_timeout_and_legacy_results_stay_scored():
    # TIMEOUT is a limit (graded on workspace artifacts); a missing
    # termination_reason is a pre-classification run. Both stay scored.
    results = [
        _r("PASS", termination_reason="OK"),
        _r("FAIL", termination_reason="TIMEOUT"),
        _r("FAIL"),
    ]
    pct, n_pass, n_total = weighted_score(results, EQUAL)
    assert (n_pass, n_total) == (1, 3)
    assert n_non_genuine(results) == 0


def test_scorecard_reports_non_genuine_count():
    results = [_r("PASS"), _r("PASS", termination_reason="INFRA_ERROR")]
    run = {"path": "x", "id": "r", "backend": "copilot", "mode": "proof-completion", "results": results}
    card = scorecard_md(run, EQUAL, "equal")
    assert "**Pass rate**: 1/1 (100.0%)" in card
    assert "1 infra/quota-cut (excluded — re-run)" in card


def test_scorecard_excludes_skip_and_reports_it():
    # Module A: PASS + SKIP -> 1/1 (skip gone). Module B: all SKIP -> absent.
    results = [_r("PASS", module="A"), _r("SKIP", module="A"), _r("SKIP", module="B")]
    run = {"path": "x/results.json", "id": "x", "backend": "codex", "mode": "proof-completion", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "**Pass rate**: 1/1 (100.0%) · 2 skipped" in md
    assert "| A | 1 | 1 | 100.0% |" in md  # skip not counted against module A
    assert "| B |" not in md  # a fully-skipped module drops out of the table
    assert "| **Total** | **1** | **1** | **100.0%** |" in md


def test_scorecard_no_skip_has_no_skipped_note():
    results = [_r("PASS"), _r("FAIL")]
    run = {"path": "x/results.json", "id": "x", "backend": "codex", "mode": "proof-completion", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "**Pass rate**: 1/2 (50.0%)" in md
    assert "skipped" not in md


def test_comparison_discloses_skip_inline():
    runs = [
        {"id": "r1", "backend": "codex", "mode": "proof-completion", "results": [_r("PASS"), _r("FAIL"), _r("SKIP")]},
        {"id": "r2", "backend": "claude_code", "mode": "proof-completion", "results": [_r("PASS"), _r("PASS")]},
    ]
    md = comparison_md(runs, EQUAL, "equal")
    assert "| r1 | codex | proof-completion | 50.0% | 1/2 (+1 skipped) |" in md
    assert "| r2 | claude_code | proof-completion | 100.0% | 2/2 |" in md  # no note when nothing skipped


# --- continuations are a separate metric, never a replacement for pass@1 ---


def _cont(*verdicts):
    return [{"round": i + 1, "check_verdict": v} for i, v in enumerate(verdicts)]


# A chain ended by a non-genuine round (the runner stops continuing on these).
CUT_CHAIN = [{"round": 1, "check_verdict": "ERROR", "termination_reason": "QUOTA_EXHAUSTED"}]


def test_continuation_passed_predicates():
    recovered = _r("FAIL", continuations=_cont("FAIL", "PASS"))
    still_failing = _r("FAIL", continuations=_cont("FAIL"))
    assert continuation_passed(recovered) and is_pass_with_continuations(recovered)
    assert not continuation_passed(still_failing) and not is_pass_with_continuations(still_failing)
    assert not continuation_passed(_r("FAIL"))  # no rounds recorded
    assert is_pass_with_continuations(_r("PASS"))  # first-attempt pass counts too


def test_weighted_score_with_continuations_same_denominator():
    # pass@1 and the continuation rate share the scored set (non-genuine excluded).
    results = [
        _r("PASS"),
        _r("FAIL", continuations=_cont("PASS")),
        _r("FAIL", continuations=_cont("FAIL")),
        _r("FAIL", termination_reason="INFRA_ERROR"),
    ]
    assert weighted_score(results, EQUAL) == (100.0 / 3, 1, 3)
    assert weighted_score(results, EQUAL, passed=is_pass_with_continuations) == (200.0 / 3, 2, 3)


def test_continuation_interrupted_only_for_unresolved_cut_chains():
    # Interrupted = the chain-ending round was infra/quota-cut with no PASS.
    assert continuation_interrupted(_r("FAIL", continuations=CUT_CHAIN))
    # An exhausted budget of genuine rounds is a real continuation failure.
    assert not continuation_interrupted(_r("FAIL", continuations=_cont("FAIL", "FAIL")))
    # A recovered chain resolved, however its stream ended.
    assert not continuation_interrupted(_r("FAIL", continuations=_cont("FAIL", "PASS")))
    assert not continuation_interrupted(_r("FAIL"))  # no rounds recorded


def test_continuation_budget_uniform_or_none():
    assert continuation_budget([_r("FAIL", max_continuations=3), _r("PASS")]) == 3
    assert continuation_budget([_r("FAIL", max_continuations=3), _r("FAIL", max_continuations=5)]) is None
    assert continuation_budget([_r("FAIL")]) is None  # legacy results: no budget recorded


def test_scorecard_reports_continuation_rate_separately():
    results = [_r("FAIL", continuations=_cont("PASS")), _r("FAIL")]
    run = {"path": "x", "id": "r", "backend": "copilot", "mode": "proof-completion", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "**Pass rate**: 0/2 (0.0%)" in md  # pass@1 stays first-attempt only
    assert "**Pass rate with continuations**: 1/2 (50.0%) — 1 recovered by continuation" in md


def test_scorecard_labels_continuation_budget_and_excludes_cut_chains():
    # The rate states its budget (≤N), and an interrupted chain is dropped from
    # numerator AND denominator with a disclosed count — never a silent failure.
    results = [
        _r("FAIL", continuations=_cont("PASS"), max_continuations=3),
        _r("FAIL", continuations=CUT_CHAIN, max_continuations=3),
        _r("FAIL"),
    ]
    run = {"path": "x", "id": "r", "backend": "copilot", "mode": "proof-completion", "results": results}
    md = scorecard_md(run, EQUAL, "equal")
    assert "**Pass rate**: 0/3 (0.0%)" in md  # the cut chain's genuine first FAIL stays scored
    assert (
        "**Pass rate with continuations (≤3)**: 1/2 (50.0%) — 1 recovered by continuation "
        "(pass@1 above is first-attempt only) · 1 chain(s) infra/quota-cut (excluded — re-run)"
    ) in md


def test_scorecard_without_continuations_has_no_continuation_line():
    results = [_r("PASS"), _r("FAIL")]
    run = {"path": "x", "id": "r", "backend": "copilot", "mode": "proof-completion", "results": results}
    assert "continuation" not in scorecard_md(run, EQUAL, "equal")


def test_comparison_discloses_continuation_recoveries_inline():
    # The budget is part of the result: +1 recovery out of ≤1 round and out of
    # ≤10 must not render identically. Legacy results without a recorded budget
    # fall back to the unlabeled note.
    runs = [
        {
            "id": "r1",
            "backend": "codex",
            "mode": "proof-completion",
            "results": [_r("PASS"), _r("FAIL", continuations=_cont("PASS"), max_continuations=3)],
        },
        {
            "id": "r2",
            "backend": "copilot",
            "mode": "proof-completion",
            "results": [_r("PASS"), _r("FAIL", continuations=_cont("PASS"))],  # legacy: no budget recorded
        },
        {"id": "r3", "backend": "claude_code", "mode": "proof-completion", "results": [_r("PASS"), _r("FAIL")]},
    ]
    md = comparison_md(runs, EQUAL, "equal")
    assert "| r1 | codex | proof-completion | 50.0% | 1/2 (+1 via ≤3 continuations) |" in md
    assert "| r2 | copilot | proof-completion | 50.0% | 1/2 (+1 via continuation) |" in md
    assert "| r3 | claude_code | proof-completion | 50.0% | 1/2 |" in md  # no note without rounds


def test_comparison_discloses_interrupted_chains_inline():
    # "(+0 via continuation)" alone would hide that the chain was infra/quota-cut
    # rather than genuinely exhausted — the cut count must appear next to it.
    runs = [
        {
            "id": "r1",
            "backend": "codex",
            "mode": "proof-completion",
            "results": [_r("PASS"), _r("FAIL", continuations=CUT_CHAIN)],
        },
    ]
    md = comparison_md(runs, EQUAL, "equal")
    assert "| r1 | codex | proof-completion | 50.0% | 1/2 (+0 via continuation) (+1 chain(s) cut) |" in md


# --- load_run / main entry point ------------------------------------------


def test_load_run_from_file_path(tmp_path):
    f = tmp_path / "results.json"
    f.write_text(json.dumps([_r("PASS", backend="codex", mode="proof-completion")]))
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
    d = _write_run(tmp_path, "run1", [_r("PASS", backend="codex", mode="proof-completion"), _r("FAIL")])
    monkeypatch.setattr(sys, "argv", ["tlaps-bench score", d])
    assert main() == 0
    out = capsys.readouterr().out
    assert "# Scorecard" in out
    assert "**Pass rate**: 1/2 (50.0%)" in out


def test_main_multiple_prints_comparison(tmp_path, monkeypatch, capsys):
    d1 = _write_run(tmp_path, "run1", [_r("PASS", backend="codex", mode="proof-completion")])
    d2 = _write_run(tmp_path, "run2", [_r("FAIL", backend="codex", mode="proof-completion")])
    monkeypatch.setattr(sys, "argv", ["tlaps-bench score", d1, d2])
    assert main() == 0
    assert "# Comparison — 2 runs" in capsys.readouterr().out


def test_main_missing_path_exits_1(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(sys, "argv", ["tlaps-bench score", str(tmp_path / "nope")])
    assert main() == 1
    assert "no results.json" in capsys.readouterr().err
