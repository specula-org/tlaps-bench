"""Score benchmark results from one or more results.json files.

``tlaps-bench run`` writes a machine-readable ``results.json`` per run. This
reads one or more of them and prints a Markdown scorecard. It is pure and
offline — no network, no API keys — so metrics can be (re)computed cheaply
without re-running the (expensive) agents.

PASS/FAIL: a task counts as passed iff its ``check_verdict`` is exactly
``"PASS"``. Every other verdict — FAIL, CHEATING, TIMEOUT, ERROR — counts as
not passed. CHEATING is not a separate category here: a cheat is just a failure.

SKIP is one exception: an operator marks a benchmark ``SKIP`` to exclude it from
scoring (e.g. a theorem known to time out for reasons outside the agent's
control). A skipped task is in neither the numerator nor the denominator — it is
dropped from the pass rate entirely, not counted as a failure — and the count is
reported separately so nothing is hidden.

Non-genuine runs are the other exception: a result whose ``termination_reason``
is ``INFRA_ERROR`` or ``QUOTA_EXHAUSTED`` was cut short by infrastructure or a
provider cap, so the verdict is not a capability signal. These are excluded from
the numerator and denominator — like SKIP — and reported separately as needing a
re-run. TIMEOUT is a limit, not infrastructure: the agent worked and is graded on
what it left in the workspace, so it stays scored.

Continuations (``tlaps-bench run --max-continuations``) are a separate metric,
never a replacement: ``check_verdict`` always holds the FIRST attempt's verdict,
so the pass rate above stays pass@1. When a run recorded continuation rounds
(``result["continuations"]``), a second, clearly-labeled "with continuations"
rate is reported (with the run's ≤N budget), counting a task as passed if any
round reached PASS — the gap between the two is how often a first-attempt
failure was an early stop rather than an inability. A chain cut short by
infra/quota before resolving is interrupted, not failed: like a non-genuine
first attempt it is excluded from the continuation rate and reported separately
(see ``continuation_interrupted``).

Pluggable scoring: a scorer assigns a non-negative weight to each task; the
score of a group of tasks is

    100 * (sum of weights of passed tasks) / (sum of all weights)

The default ``equal`` scorer gives every task weight 1, so the score is simply
the percentage of tasks passed. To add a scheme (e.g. weight by proof
obligations), register another weight function in ``SCORERS`` and select it with
``--scoring``.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
from collections import defaultdict
from collections.abc import Callable

PASS_VERDICT = "PASS"
SKIP_VERDICT = "SKIP"
NON_GENUINE_TERMINATIONS = {"INFRA_ERROR", "QUOTA_EXHAUSTED"}
COST_TIME_BACKENDS = {
    "codex",
    "claude_code",
    "copilot",
    "copilot_oneshot",
    "cursor",
    "litellm",
    "litellm_oneshot",
    "pi",
}


def is_pass(result: dict) -> bool:
    """A task passed iff its verdict is exactly PASS (CHEATING/FAIL/... do not)."""
    return result.get("check_verdict") == PASS_VERDICT


def is_skipped(result: dict) -> bool:
    """A task is SKIP iff an operator excluded it from scoring (see module doc)."""
    return result.get("check_verdict") == SKIP_VERDICT


def is_non_genuine(result: dict) -> bool:
    """A run cut short by infra/quota. Missing termination_reason means legacy
    result files stay scored."""
    return result.get("termination_reason") in NON_GENUINE_TERMINATIONS


def continuation_passed(result: dict) -> bool:
    """Whether any continuation round (--max-continuations) reached PASS.

    A round's PASS means the grader verified the proof in the workspace, so it
    is ground truth regardless of how that round's event stream terminated."""
    return any(r.get("check_verdict") == PASS_VERDICT for r in result.get("continuations") or [])


def is_pass_with_continuations(result: dict) -> bool:
    """PASS on the first attempt or on any continuation round — the predicate
    behind the separate "with continuations" rate (pass@1 uses is_pass)."""
    return is_pass(result) or continuation_passed(result)


def continuation_interrupted(result: dict) -> bool:
    """Whether the continuation chain was cut short by infra/quota before it
    could resolve: no round passed and the chain-ending round is non-genuine.

    Like a non-genuine first attempt, the outcome is indeterminate — neither a
    recovery nor an exhausted budget — so the continuation rate excludes it and
    reports it separately (rerun the benchmark with --resume)."""
    rounds = result.get("continuations") or []
    return bool(rounds) and is_non_genuine(rounds[-1]) and not continuation_passed(result)


def continuation_budget(results: list[dict]) -> int | None:
    """The run's --max-continuations budget, when recorded and uniform across
    results. Mixed budgets (e.g. a run resumed with a different flag) yield
    None and reports omit the ≤N label."""
    budgets = {r["max_continuations"] for r in results if r.get("max_continuations")}
    return budgets.pop() if len(budgets) == 1 else None


def continuation_rate_line(results: list[dict], weight: Callable[[dict], float], n_pass: int) -> str | None:
    """The "with continuations" pass-rate line shared by summary.md and the
    scorecard, or None when no continuation rounds were recorded. Interrupted
    chains are excluded from the rate and disclosed; ``n_pass`` is the pass@1
    count the recovery delta is measured against."""
    if not any(r.get("continuations") for r in results):
        return None
    resolved = [r for r in results if not continuation_interrupted(r)]
    cpct, cn_pass, cn_total = weighted_score(resolved, weight, passed=is_pass_with_continuations)
    budget = continuation_budget(results)
    label = f" (≤{budget})" if budget else ""
    line = (
        f"**Pass rate with continuations{label}**: {cn_pass}/{cn_total} ({cpct:.1f}%) — "
        f"{cn_pass - n_pass} recovered by continuation (pass@1 above is first-attempt only)"
    )
    n_cut = sum(1 for r in results if continuation_interrupted(r))
    if n_cut:
        line += f" · {n_cut} chain(s) infra/quota-cut (excluded — re-run)"
    return line


def n_skipped(results: list[dict]) -> int:
    """How many tasks were operator-excluded from scoring."""
    return sum(1 for r in results if is_skipped(r))


def n_non_genuine(results: list[dict]) -> int:
    """How many results are excluded as non-genuine (need a re-run)."""
    return sum(1 for r in results if is_non_genuine(r))


# A scorer maps one task result to a non-negative weight; the group score is the
# weighted pass fraction. Add an entry here to define a new scheme, then select
# it with --scoring.
SCORERS: dict[str, Callable[[dict], float]] = {
    "equal": lambda r: 1.0,  # every task counts the same; score = % passed
}


def weighted_score(
    results: list[dict], weight: Callable[[dict], float], passed: Callable[[dict], bool] = is_pass
) -> tuple[float, int, int]:
    """Return (score_percent, n_passed, n_total) over the scored tasks.

    SKIP and non-genuine tasks are dropped first, so ``n_total`` is the number
    of *scored* tasks (excluded ones count toward neither the pass count nor the
    denominator). ``passed`` is the pass predicate: the default scores pass@1;
    the "with continuations" rate passes ``is_pass_with_continuations`` after
    also dropping interrupted chains (see continuation_rate_line).
    """
    scored = [r for r in results if not is_skipped(r) and not is_non_genuine(r)]
    n_total = len(scored)
    n_pass = sum(1 for r in scored if passed(r))
    total_w = sum(max(weight(r), 0.0) for r in scored)
    pass_w = sum(max(weight(r), 0.0) for r in scored if passed(r))
    pct = (100.0 * pass_w / total_w) if total_w > 0 else 0.0
    return pct, n_pass, n_total


def load_run(path: str) -> dict:
    """Load a results.json (``path`` may be the file itself or its run dir).

    Returns {"path", "id", "backend", "mode", "results"}.
    """
    json_path = os.path.join(path, "results.json") if os.path.isdir(path) else path
    if not os.path.isfile(json_path):
        raise FileNotFoundError(f"no results.json at {path}")
    with open(json_path) as f:
        results = json.load(f)
    backends = sorted({r.get("backend") for r in results if r.get("backend")})
    modes = sorted({r.get("mode") for r in results if r.get("mode")})
    run_dir = os.path.dirname(os.path.abspath(json_path))
    return {
        "path": json_path,
        "id": os.path.basename(run_dir) or run_dir,
        "backend": "+".join(backends) or "?",
        "mode": "+".join(modes) or "?",
        "results": results,
    }


def _sum_metric(results: list[dict], field: str) -> float | None:
    """Sum a required non-negative metric without turning missing data into zero."""

    if not results:
        return None
    values: list[float] = []
    for result in results:
        value = result.get(field)
        if not isinstance(value, (int, float)) or isinstance(value, bool):
            return None
        try:
            parsed = float(value)
        except (OverflowError, ValueError):
            return None
        if parsed < 0 or not math.isfinite(parsed):
            return None
        values.append(parsed)
    return sum(values)


def _has_equivalent_cost(results: list[dict]) -> bool:
    return any("equivalent_cost_usd" in result for result in results)


def _totals(results: list[dict]) -> tuple[int, int, float | None, float | None]:
    in_tok = sum(r.get("input_tokens", 0) for r in results)
    out_tok = sum(r.get("output_tokens", 0) for r in results)
    if not _has_equivalent_cost(results):
        return in_tok, out_tok, sum(r.get("time_secs", 0) for r in results), None
    formal = [result for result in results if not is_skipped(result) and not is_non_genuine(result)]
    secs = _sum_metric(formal, "time_secs")
    equivalent_cost_usd = _sum_metric(formal, "equivalent_cost_usd")
    return in_tok, out_tok, secs, equivalent_cost_usd


def _cost_warnings(results: list[dict]) -> list[tuple[str, str]]:
    warnings: list[tuple[str, str]] = []
    for result in results:
        if is_skipped(result) or is_non_genuine(result):
            continue
        usage = result.get("usage")
        raw_warnings = usage.get("warnings") if isinstance(usage, dict) else None
        if not isinstance(raw_warnings, list):
            continue
        benchmark = str(result.get("benchmark", "?"))
        warnings.extend(
            (benchmark, warning)
            for warning in raw_warnings
            if isinstance(warning, str) and warning.startswith("equivalent cost ")
        )
    return warnings


def _format_time(secs: float | None) -> str:
    return "unavailable" if secs is None else f"{secs:,.1f}s"


def _format_cost(cost_usd: float | None) -> str:
    if cost_usd is None:
        return "unavailable"
    if cost_usd == 0 or cost_usd >= 0.000001:
        return f"${cost_usd:,.6f}"
    return f"${cost_usd:.6g}"


def scorecard_md(run: dict, weight: Callable[[dict], float], scoring_name: str) -> str:
    """Markdown scorecard for a single run: overall pass rate + per-module table."""
    results = run["results"]
    pct, n_pass, n_total = weighted_score(results, weight)
    skipped = n_skipped(results)
    non_genuine = n_non_genuine(results)
    in_tok, out_tok, secs, equivalent_cost_usd = _totals(results)
    has_equivalent_cost = _has_equivalent_cost(results)

    pass_line = f"**Pass rate**: {n_pass}/{n_total} ({pct:.1f}%)"
    if skipped:
        pass_line += f" · {skipped} skipped"
    if non_genuine:
        pass_line += f" · {non_genuine} infra/quota-cut (excluded — re-run)"
    lines = [
        f"# Scorecard — {run['backend']} / {run['mode']}",
        "",
        f"**Source**: {run['path']}",
        pass_line,
    ]
    # Separate, clearly-labeled metric — the pass rate above stays pass@1.
    cont_line = continuation_rate_line(results, weight, n_pass)
    if cont_line:
        lines.append(cont_line)
    if has_equivalent_cost:
        lines.append(f"**Tokens**: {in_tok:,} in / {out_tok:,} out")
        lines.append(f"**Total task time**: {_format_time(secs)}")
        lines.append(f"**Equivalent cost**: {_format_cost(equivalent_cost_usd)}")
    else:
        lines.append(f"**Cost**: {in_tok:,} in / {out_tok:,} out tokens · {secs:,.0f}s total")
    if scoring_name != "equal":
        lines.append(f"**Scoring**: {scoring_name} (weighted)")
    lines += [
        "",
        "## By module",
        "",
        "| Module | Passed | Total | Pass % |",
        "|--------|-------:|------:|-------:|",
    ]
    by_module: dict[str, list[dict]] = defaultdict(list)
    for r in results:
        if is_skipped(r) or is_non_genuine(r):
            continue  # fully-excluded modules drop out of the table entirely
        by_module[r.get("module") or "?"].append(r)
    for module in sorted(by_module):
        mpct, mp, mt = weighted_score(by_module[module], weight)
        lines.append(f"| {module} | {mp} | {mt} | {mpct:.1f}% |")
    lines.append(f"| **Total** | **{n_pass}** | **{n_total}** | **{pct:.1f}%** |")
    lines.append("")
    cost_warnings = _cost_warnings(results) if has_equivalent_cost else []
    if cost_warnings:
        lines += ["## Cost warnings", ""]
        lines.extend(f"- `{benchmark}`: {warning}" for benchmark, warning in cost_warnings)
        lines.append("")
    return "\n".join(lines)


def comparison_md(runs: list[dict], weight: Callable[[dict], float], scoring_name: str) -> str:
    """Markdown comparison table across several runs (one row per run)."""
    lines = [f"# Comparison — {len(runs)} runs", ""]
    if scoring_name != "equal":
        lines += [f"**Scoring**: {scoring_name} (weighted)", ""]
    show_equivalent_cost = any(_has_equivalent_cost(run["results"]) for run in runs)
    if show_equivalent_cost:
        lines += [
            "| Run | Backend | Mode | Pass % | Passed/Total | Tokens (in/out) | Time | Equivalent cost |",
            "|-----|---------|------|-------:|-------------:|-----------------|-----:|----------------:|",
        ]
    else:
        lines += [
            "| Run | Backend | Mode | Pass % | Passed/Total | Tokens (in/out) | Time |",
            "|-----|---------|------|-------:|-------------:|-----------------|-----:|",
        ]
    for run in runs:
        pct, n_pass, n_total = weighted_score(run["results"], weight)
        in_tok, out_tok, secs, equivalent_cost_usd = _totals(run["results"])
        run_has_equivalent_cost = _has_equivalent_cost(run["results"])
        if show_equivalent_cost and not run_has_equivalent_cost and run["backend"] in COST_TIME_BACKENDS:
            formal = [result for result in run["results"] if not is_skipped(result) and not is_non_genuine(result)]
            secs = _sum_metric(formal, "time_secs")
        passed_total = f"{n_pass}/{n_total}"
        skipped = n_skipped(run["results"])
        if skipped:
            passed_total += f" (+{skipped} skipped)"
        non_genuine = n_non_genuine(run["results"])
        if non_genuine:
            passed_total += f" (+{non_genuine} infra-cut)"
        if any(r.get("continuations") for r in run["results"]):
            _, cn_pass, _ = weighted_score(run["results"], weight, passed=is_pass_with_continuations)
            # Name the budget: +1 recovery out of ≤1 round and out of ≤10 are
            # different results, and rows in this table exist to be compared.
            budget = continuation_budget(run["results"])
            if budget:
                passed_total += f" (+{cn_pass - n_pass} via ≤{budget} continuations)"
            else:
                passed_total += f" (+{cn_pass - n_pass} via continuation)"
            n_cut = sum(1 for r in run["results"] if continuation_interrupted(r))
            if n_cut:
                passed_total += f" (+{n_cut} chain(s) cut)"
        row = (
            f"| {run['id']} | {run['backend']} | {run['mode']} | {pct:.1f}% | "
            f"{passed_total} | {in_tok:,}/{out_tok:,} | "
        )
        if show_equivalent_cost:
            time_text = (
                _format_time(secs)
                if run_has_equivalent_cost or run["backend"] in COST_TIME_BACKENDS
                else f"{secs:,.0f}s"
            )
            row += f"{time_text} | {_format_cost(equivalent_cost_usd)} |"
        else:
            row += f"{secs:,.0f}s |"
        lines.append(row)
    lines.append("")
    warnings = [
        (run["id"], benchmark, warning) for run in runs for benchmark, warning in _cost_warnings(run["results"])
    ]
    if warnings:
        lines += ["## Cost warnings", ""]
        lines.extend(f"- `{run_id}` / `{benchmark}`: {warning}" for run_id, benchmark, warning in warnings)
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="tlaps-bench score",
        description="Score benchmark results (pass rate, per-module breakdown) from results.json.",
    )
    parser.add_argument("paths", nargs="+", help="One or more results.json files or run directories")
    parser.add_argument(
        "--scoring",
        default="equal",
        choices=sorted(SCORERS),
        help="Scoring scheme (default: equal — every task weight 1, score = %% passed)",
    )
    args = parser.parse_args()

    weight = SCORERS[args.scoring]
    runs = []
    for p in args.paths:
        try:
            runs.append(load_run(p))
        except (FileNotFoundError, json.JSONDecodeError, OSError) as e:
            sys.stderr.write(f"tlaps-bench score: {e}\n")
            return 1

    if len(runs) == 1:
        print(scorecard_md(runs[0], weight, args.scoring))
    else:
        print(comparison_md(runs, weight, args.scoring))
    return 0


if __name__ == "__main__":
    sys.exit(main())
