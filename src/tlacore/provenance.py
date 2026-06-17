"""Tell apart files the benchmark *gave* the agent from files the agent *created*.

This distinction is the single most important guard against false positives.
In L2, every dependency module the benchmark provides has its proofs stripped to
``PROOF OMITTED`` *by design* — so OMITTED inside a given dependency is expected
and legitimate. The cheat (e.g. codex's ``AuxLiveness.tla``) is when the agent
*introduces a new module* containing an admitted statement and leans on it.

Provenance is a pure file-provenance question — SANY cannot answer it, because
SANY only parses whatever files are present. The authoritative source of "what
was given" is the canonical benchmark directory (``benchmark/<level>/<module>/``),
which holds the target plus exactly the dependency modules that were provided.
"""

from __future__ import annotations

import glob
import os
from dataclasses import dataclass, field

# Standard library / prover modules — never agent-created, never scanned.
STDLIB = {
    "Integers",
    "Naturals",
    "Reals",
    "Sequences",
    "FiniteSets",
    "Bags",
    "TLC",
    "TLAPS",
    "RealTime",
    "Folds",
    "Functions",
    "Json",
    "FiniteSetTheorems",
    "FunctionTheorems",
    "SequenceTheorems",
    "NaturalsInduction",
    "WellFoundedInduction",
    "BagsTheorems",
    "CommunityModules",
    # Vendored CommunityModules (lib/community/) the tlaplus/Examples imports
    # EXTEND by individual module name. Kept in sync with COMMUNITY_MODULES in
    # src/dataset/level1/generate.py.
    "SequencesExt",
    "SequencesExtTheorems",
    "FiniteSetsExt",
    "FunctionsExt",
    "BagsExt",
    "Relation",
    "Graphs",
    "GraphsExt",
    "Combinatorics",
    "DyadicRationals",
    "Bitwise",
    "Statistics",
    "VectorClocks",
    "IOUtils",
    "CSV",
    "SVG",
    "TLCExt",
    "Randomization",
}


def _module_names(tla_dir: str) -> set[str]:
    return {os.path.splitext(os.path.basename(f))[0] for f in glob.glob(os.path.join(tla_dir, "*.tla"))}


@dataclass
class Provenance:
    target: str  # the benchmark module name (e.g. "VoteProof_Liveness")
    given: set[str] = field(default_factory=set)  # module names provided by the benchmark
    agent_created: dict[str, str] = field(default_factory=dict)  # name -> .tla path

    def is_given(self, module_name: str) -> bool:
        return module_name in self.given or module_name in STDLIB

    def is_agent_created(self, module_name: str) -> bool:
        return module_name in self.agent_created


def classify(solution_dir: str, target_name: str, benchmark_dir: str | None = None) -> Provenance:
    """Classify the .tla files in ``solution_dir`` as given vs agent-created.

    Args:
        solution_dir: the result directory (contains the solution, benchmark.tla,
            given dependency modules, and any agent-created modules).
        target_name: the benchmark module name (its solution file is the target,
            not a dependency).
        benchmark_dir: the canonical ``benchmark/<level>/<module>/`` directory.
            When given, its module set is the authoritative "given" oracle.
            When None, we fall back to treating everything present *except*
            modules that don't appear in the baseline benchmark.tla as given —
            a weaker heuristic; prefer always passing ``benchmark_dir``.
    """
    prov = Provenance(target=target_name)

    if benchmark_dir and os.path.isdir(benchmark_dir):
        # Authoritative: given = whatever modules the canonical benchmark ships,
        # minus the target itself.
        prov.given = _module_names(benchmark_dir) - {target_name}
    else:
        # Fallback oracle: the baseline benchmark.tla in the solution dir tells
        # us nothing about deps directly, so treat sibling modules present in
        # both dirs as given and leave the rest to be flagged as created below.
        prov.given = set()

    # Anything physically present in the solution dir that is neither the target,
    # a benchmark scaffolding file, a given dependency, nor stdlib is "created".
    for f in glob.glob(os.path.join(solution_dir, "*.tla")):
        mod = os.path.splitext(os.path.basename(f))[0]
        if mod in (target_name, "benchmark", "solution"):
            continue
        if mod in prov.given or mod in STDLIB:
            continue
        prov.agent_created[mod] = f

    return prov
