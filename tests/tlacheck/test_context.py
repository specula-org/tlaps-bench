"""Baseline-provenance guard for build_context (N1 regression).

The cheat-detection baseline must come from the read-only ``benchmark_dir``
(the ``/benchmark:ro`` mount), never from the agent-writable workspace copy
``solution_dir/benchmark.tla``. An agent that weakens a theorem and rewrites
its own ``benchmark.tla`` must not thereby move the goalposts for the checker.

Run: PYTHONPATH=src python3 -m pytest tests/tlacheck/test_context.py
(or just: PYTHONPATH=src python3 tests/tlacheck/test_context.py)
"""

from pathlib import Path

import pytest

from tlacheck import context as context_module
from tlacheck.context import build_context
from tlacore.sany.dump import SanyRun, SanyStatus, SanyUnavailable

# Clean baseline shipped under benchmark_dir (read-only mount).
CANONICAL = """\
---- MODULE Foo ----
\\* CANONICAL baseline.
EXTENDS Naturals

THEOREM MainResult == \\A n \\in Nat : n + 0 = n
====
"""

# Weakened copy the agent rewrote into its own workspace.
TAMPERED = """\
---- MODULE Foo ----
\\* TAMPERED baseline written by the agent.
EXTENDS Naturals

THEOREM MainResult == TRUE
====
"""

SOLUTION = """\
---- MODULE Foo ----
EXTENDS Naturals

THEOREM MainResult == TRUE
  OBVIOUS
====
"""


def _layout(tmp_path):
    """benchmark_dir holds the clean Foo.tla; solution_dir holds the agent's
    Foo.tla plus a TAMPERED benchmark.tla."""
    bench = tmp_path / "benchmark"
    sol = tmp_path / "solution"
    bench.mkdir()
    sol.mkdir()
    (bench / "Foo.tla").write_text(CANONICAL)
    (sol / "Foo.tla").write_text(SOLUTION)
    (sol / "benchmark.tla").write_text(TAMPERED)
    return str(bench), str(sol)


def test_baseline_comes_from_benchmark_dir(tmp_path):
    bench, sol = _layout(tmp_path)
    ctx = build_context(sol, "Foo", benchmark_dir=bench)

    # baseline_source is what the text-signature rules slice from, and it is
    # read straight from base_path -- so pinning it pins base_path itself
    # (hence the parsed ``ctx.baseline`` too, the same variable).
    assert "TAMPERED" not in ctx.baseline_source, "baseline read from agent-writable benchmark.tla"
    assert ctx.baseline_source == CANONICAL, "baseline not taken from read-only benchmark_dir"
    assert ctx.benchmark_dir == bench


def test_without_benchmark_dir_falls_back_to_workspace(tmp_path):
    # Negative control: with no benchmark_dir the only baseline available is the
    # workspace copy -- proving the assertion above actually discriminates.
    _bench, sol = _layout(tmp_path)
    ctx = build_context(sol, "Foo")
    assert "TAMPERED" in ctx.baseline_source
    assert ctx.baseline_source == TAMPERED


def test_context_distinguishes_sany_rejection_from_unavailable(tmp_path, monkeypatch):
    _bench, sol = _layout(tmp_path)
    invalid = SanyRun(SanyStatus.INVALID, ("sany",), 3, "", "duplicate", "SANY rejected module")
    monkeypatch.setattr(context_module, "run_normalized", lambda *_args, **_kwargs: invalid)

    ctx = build_context(sol, "Foo")

    assert ctx.sany_status is SanyStatus.INVALID
    assert not ctx.sany_ok

    unavailable = SanyRun(SanyStatus.UNAVAILABLE, ("sany",), None, "", "", "tool missing")
    monkeypatch.setattr(context_module, "run_normalized", lambda *_args, **_kwargs: unavailable)
    with pytest.raises(SanyUnavailable, match="tool missing"):
        build_context(sol, "Foo")


def test_context_parses_with_its_own_dependency_order(tmp_path):
    benchmark = tmp_path / "benchmark"
    solution = tmp_path / "solution"
    benchmark.mkdir()
    solution.mkdir()
    module = "---- MODULE Foo ----\nEXTENDS Dep\nTHEOREM Goal == Value PROOF OBVIOUS\n====\n"
    (benchmark / "Foo.tla").write_text(module)
    (benchmark / "Dep.tla").write_text("---- MODULE Dep ----\nValue == TRUE\n====\n")
    (solution / "Foo.tla").write_text(module)
    (solution / "Dep.tla").write_text("---- MODULE Dep ----\nValue == [a |-> 1, a |-> 2]\n====\n")

    ctx = build_context(str(solution), "Foo", benchmark_dir=str(benchmark))

    assert ctx.sany_status is SanyStatus.INVALID


if __name__ == "__main__":
    import tempfile

    for fn in (test_baseline_comes_from_benchmark_dir, test_without_benchmark_dir_falls_back_to_workspace):
        with tempfile.TemporaryDirectory() as d:
            fn(Path(d))
    print("ok: build_context baseline-provenance tests passed")
