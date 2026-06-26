"""Score benchmark results from one or more results.json files.

``tlaps-bench run`` writes a machine-readable ``results.json`` per run. This
reads one or more of them and prints a Markdown scorecard. It is pure and
offline — no network, no API keys — so metrics can be (re)computed cheaply
without re-running the (expensive) agents.

PASS/FAIL: a task counts as passed iff its ``check_verdict`` is exactly
``"PASS"``. Every other verdict — FAIL, CHEATING, TIMEOUT, ERROR — counts as
not passed. CHEATING is not a separate category here: a cheat is just a failure.

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
import os
import sys
from collections import defaultdict
from collections.abc import Callable

PASS_VERDICT = "PASS"


def is_pass(result: dict) -> bool:
    """A task passed iff its verdict is exactly PASS (CHEATING/FAIL/... do not)."""
    return result.get("check_verdict") == PASS_VERDICT


# A scorer maps one task result to a non-negative weight; the group score is the
# weighted pass fraction. Add an entry here to define a new scheme, then select
# it with --scoring.
SCORERS: dict[str, Callable[[dict], float]] = {
    "equal": lambda r: 1.0,  # every task counts the same; score = % passed
}


def weighted_score(results: list[dict], weight: Callable[[dict], float]) -> tuple[float, int, int]:
    """Return (score_percent, n_passed, n_total) for a list of task results."""
    n_total = len(results)
    n_pass = sum(1 for r in results if is_pass(r))
    total_w = sum(max(weight(r), 0.0) for r in results)
    pass_w = sum(max(weight(r), 0.0) for r in results if is_pass(r))
    pct = (100.0 * pass_w / total_w) if total_w > 0 else 0.0
    return pct, n_pass, n_total


def load_run(path: str) -> dict:
    """Load a results.json (``path`` may be the file itself or its run dir).

    Returns {"path", "id", "backend", "level", "results"}.
    """
    json_path = os.path.join(path, "results.json") if os.path.isdir(path) else path
    if not os.path.isfile(json_path):
        raise FileNotFoundError(f"no results.json at {path}")
    with open(json_path) as f:
        results = json.load(f)
    backends = sorted({r.get("backend") for r in results if r.get("backend")})
    levels = sorted({r.get("level") for r in results if r.get("level")})
    run_dir = os.path.dirname(os.path.abspath(json_path))
    return {
        "path": json_path,
        "id": os.path.basename(run_dir) or run_dir,
        "backend": "+".join(backends) or "?",
        "level": "+".join(levels) or "?",
        "results": results,
    }


def _cost(results: list[dict]) -> tuple[int, int, float]:
    in_tok = sum(r.get("input_tokens", 0) for r in results)
    out_tok = sum(r.get("output_tokens", 0) for r in results)
    secs = sum(r.get("time_secs", 0) for r in results)
    return in_tok, out_tok, secs


def scorecard_md(run: dict, weight: Callable[[dict], float], scoring_name: str) -> str:
    """Markdown scorecard for a single run: overall pass rate + per-module table."""
    results = run["results"]
    pct, n_pass, n_total = weighted_score(results, weight)
    in_tok, out_tok, secs = _cost(results)

    lines = [
        f"# Scorecard — {run['backend']} / {run['level']}",
        "",
        f"**Source**: {run['path']}",
        f"**Pass rate**: {n_pass}/{n_total} ({pct:.1f}%)",
        f"**Cost**: {in_tok:,} in / {out_tok:,} out tokens · {secs:,.0f}s total",
    ]
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
        by_module[r.get("module") or "?"].append(r)
    for module in sorted(by_module):
        mpct, mp, mt = weighted_score(by_module[module], weight)
        lines.append(f"| {module} | {mp} | {mt} | {mpct:.1f}% |")
    lines.append(f"| **Total** | **{n_pass}** | **{n_total}** | **{pct:.1f}%** |")
    lines.append("")
    return "\n".join(lines)


def comparison_md(runs: list[dict], weight: Callable[[dict], float], scoring_name: str) -> str:
    """Markdown comparison table across several runs (one row per run)."""
    lines = [f"# Comparison — {len(runs)} runs", ""]
    if scoring_name != "equal":
        lines += [f"**Scoring**: {scoring_name} (weighted)", ""]
    lines += [
        "| Run | Backend | Level | Pass % | Passed/Total | Tokens (in/out) | Time |",
        "|-----|---------|-------|-------:|-------------:|-----------------|-----:|",
    ]
    for run in runs:
        pct, n_pass, n_total = weighted_score(run["results"], weight)
        in_tok, out_tok, secs = _cost(run["results"])
        lines.append(
            f"| {run['id']} | {run['backend']} | {run['level']} | {pct:.1f}% | "
            f"{n_pass}/{n_total} | {in_tok:,}/{out_tok:,} | {secs:,.0f}s |"
        )
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
