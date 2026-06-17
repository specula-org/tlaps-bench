"""Everything a rule needs to judge one solution, prepared once.

The context gathers the "ground truth" so individual rules stay small and
declarative: the parsed solution module, the baseline benchmark module (to
subtract what was *given*), file provenance (given deps vs agent-created
modules), and — optionally — the tlapm ``--summary`` accounting.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass, field

from tlacore.model import Module
from tlacore.provenance import Provenance, classify
from tlacore.sany.dump import try_dump_normalized
from tlacore.source import slice_loc
from tlacore.tlapm.summary import Summary, run_summary

_WS = re.compile(r"\s+")


def _norm(text: str) -> str:
    return _WS.sub(" ", text).strip()


@dataclass
class CheckContext:
    target_name: str  # benchmark module name
    solution_dir: str  # result dir holding the submission
    solution: Module | None  # parsed solution module (None if SANY failed)
    baseline: Module | None  # parsed benchmark.tla (given baseline)
    provenance: Provenance
    benchmark_dir: str | None = None  # canonical benchmark/<level>/<module>/
    solution_source: str = ""  # raw text of the solution file
    baseline_source: str = ""  # raw text of benchmark.tla
    sany_ok: bool = True  # did Java SANY parse the solution?
    # tlapm authoritative fallback (used when sany_ok is False): tlapm's own
    # parser accepts everything it considers valid, so --summary works where
    # Java SANY (stricter) refuses. Keyed: "" = solution, mod name = agent module.
    summaries: dict = field(default_factory=dict)
    agent_modules: dict[str, Module] = field(default_factory=dict)  # name -> parsed
    summary: Summary | None = None
    tlapm_output: str = ""
    tlapm_passed: bool = False

    # -- derived helpers -----------------------------------------------------

    def baseline_admitted_names(self) -> set[str]:
        """Names of theorems already admitted in the given baseline (allowed)."""
        if not self.baseline:
            return set()
        return {t.name for t in self.baseline.admitted_theorems if t.name}

    def baseline_axiom_names(self) -> set[str]:
        if not self.baseline:
            return set()
        return {a.name for a in self.baseline.assumes if a.name}

    # -- text signatures (match unnamed declarations against the baseline) ----
    #
    # Named declarations are matched by name; UNNAMED ones (e.g. `ASSUME N \in
    # Nat`, or an unnamed `THEOREM ... PROOF OMITTED` given as an L1 lemma) have
    # name == None and cannot be matched by name. We fall back to the normalized
    # statement text, sliced from source via the SANY location.

    def baseline_admitted_stmt_texts(self) -> set[str]:
        if not self.baseline or not self.baseline_source:
            return set()
        out = set()
        for t in self.baseline.admitted_theorems:
            loc = t.statement_loc or t.loc
            if loc:
                out.add(_norm(slice_loc(self.baseline_source, loc)))
        return out

    def baseline_assume_texts(self) -> set[str]:
        if not self.baseline or not self.baseline_source:
            return set()
        out = set()
        for a in self.baseline.assumes:
            if a.loc:
                out.add(_norm(slice_loc(self.baseline_source, a.loc)))
        return out

    def solution_stmt_text(self, theorem) -> str:
        loc = theorem.statement_loc or theorem.loc
        return _norm(slice_loc(self.solution_source, loc)) if loc else ""

    def solution_assume_text(self, assume) -> str:
        return _norm(slice_loc(self.solution_source, assume.loc)) if assume.loc else ""


def build_context(
    solution_dir: str,
    target_name: str,
    *,
    benchmark_dir: str | None = None,
    summary: Summary | None = None,
    tlapm_output: str = "",
    tlapm_passed: bool = False,
    solution_file: str | None = None,
    tlapm_fallback: bool = False,
    compute_summary: bool = False,
    fallback_timeout: float = 600,
) -> CheckContext:
    """Parse the solution + baseline + agent-created modules and assemble a context.

    ``benchmark_dir`` is the canonical ``benchmark/<level>/<module>/`` directory
    — strongly recommended, as it is the authoritative provenance oracle.

    If Java SANY cannot parse the solution (it is stricter than tlapm — e.g. it
    rejects bound-variable shadowing tlapm accepts) and ``tlapm_fallback`` is
    set, we run ``tlapm --summary`` on the solution and each agent-created module
    so the soundness rules can still fire from tlapm's own accounting.
    """
    sol_path = solution_file or os.path.join(solution_dir, target_name + ".tla")
    if not os.path.exists(sol_path):
        sol_path = os.path.join(solution_dir, "solution.tla")
    # Dependency search dirs: the canonical benchmark dir supplies the GIVEN
    # modules (archived result dirs often drop them, keeping only benchmark.tla
    # + solution.tla); the result dir supplies the submission and any
    # agent-created modules, and overrides on name clashes (later wins).
    dep_dirs = [d for d in (benchmark_dir, solution_dir) if d]
    solution = try_dump_normalized(sol_path, dep_dirs=dep_dirs)
    sany_ok = solution is not None

    base_path = os.path.join(solution_dir, "benchmark.tla")
    baseline = try_dump_normalized(base_path, dep_dirs=dep_dirs) if os.path.exists(base_path) else None

    def _read(p):
        try:
            return open(p, encoding="utf-8", errors="ignore").read()
        except OSError:
            return ""

    solution_source = _read(sol_path)
    baseline_source = _read(base_path) if os.path.exists(base_path) else ""

    prov = classify(solution_dir, target_name, benchmark_dir=benchmark_dir)
    agent_modules: dict[str, Module] = {}
    for name, path in prov.agent_created.items():
        m = try_dump_normalized(path, dep_dirs=dep_dirs)
        if m is not None:
            agent_modules[name] = m

    # tlapm authoritative fallback when Java SANY refused the solution.
    summaries: dict = {}
    if not sany_ok and tlapm_fallback:
        summaries[""] = _safe_summary(sol_path, solution_dir, fallback_timeout)
        if summaries[""] is not None:
            summary = summaries[""]
        # Baseline summary lets us subtract GIVEN admitted lemmas (L1 ships
        # preceding PROOF OMITTED lemmas; their lines are unchanged in the
        # solution, so a line-set diff isolates agent-introduced admissions).
        if os.path.exists(base_path):
            summaries["__baseline__"] = _safe_summary(base_path, solution_dir, fallback_timeout)
        for name, path in prov.agent_created.items():
            summaries[name] = _safe_summary(path, solution_dir, fallback_timeout)

    # When SANY parsed the solution, the structural rules don't need tlapm, but
    # the incomplete_proof rule still does (it reads tlapm's --summary to see a
    # bare QED buried inside a structured proof). Compute it on demand unless the
    # caller already supplied a parsed summary.
    if sany_ok and compute_summary and summary is None:
        summary = _safe_summary(sol_path, solution_dir, fallback_timeout)

    return CheckContext(
        target_name=target_name,
        solution_dir=solution_dir,
        solution=solution,
        baseline=baseline,
        provenance=prov,
        benchmark_dir=benchmark_dir,
        solution_source=solution_source,
        baseline_source=baseline_source,
        sany_ok=sany_ok,
        summaries=summaries,
        agent_modules=agent_modules,
        summary=summary,
        tlapm_output=tlapm_output,
        tlapm_passed=tlapm_passed,
    )


def _safe_summary(tla_path, cwd, timeout):
    try:
        return run_summary(tla_path, cwd, timeout=timeout)
    except Exception:
        return None
