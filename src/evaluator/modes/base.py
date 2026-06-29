"""Abstract base class for benchmark modes.

A `Mode` is one benchmark suite — e.g. proof-completion (proof completion) or
proof-from-scratch (proof from scratch). It owns everything that varies
between suites:

  - where the benchmark files live
  - how to tell a benchmark from a dependency file
  - which prompt template the agent receives
  - how to invoke the checker that grades the agent's output

The runner is mode-agnostic: it asks the `Mode` object for each of those.
"""

from __future__ import annotations

import glob
import os
import re
import sys
from abc import ABC

# A top-level proof goal — `THEOREM`/`LEMMA`/`COROLLARY`/`PROPOSITION` at the
# start of a logical line (optionally named). This is what makes a file a
# benchmark to be proved, as opposed to a shared model / dependency layer.
_TOP_LEVEL_GOAL = re.compile(r"^[ \t]*(THEOREM|LEMMA|COROLLARY|PROPOSITION)\b", re.MULTILINE)

# Module references that a .tla file depends on to even parse: its `EXTENDS`
# clause (a single comma-separated list, possibly wrapping across lines — `\s`
# spans newlines) and any `INSTANCE` of a module. A stray match inside a comment
# is harmless: it is only ever looked up against actual sibling files.
_EXTENDS_RE = re.compile(r"\bEXTENDS\b\s+([A-Za-z_]\w*(?:\s*,\s*[A-Za-z_]\w*)*)")
_INSTANCE_RE = re.compile(r"\bINSTANCE\s+([A-Za-z_]\w*)")


def _referenced_modules(text: str) -> set[str]:
    """Module names this source references via EXTENDS / INSTANCE."""
    names: set[str] = set()
    for m in _EXTENDS_RE.finditer(text):
        names.update(n.strip() for n in m.group(1).split(","))
    for m in _INSTANCE_RE.finditer(text):
        names.add(m.group(1))
    return names


class Mode(ABC):  # noqa: B024 - ABC used as a non-instantiable base marker; subclasses set class attrs
    name: str = ""
    description: str = ""

    def __init__(self, benchmark_root: str, checker_binary: str):
        """
        Args:
            benchmark_root: dir containing all mode subdirs
                            (e.g. /benchmark in docker, <repo>/benchmark on host).
            checker_binary: absolute path to the check_proof binary.
        """
        if not self.name:
            raise ValueError(f"{type(self).__name__} must set `name`")
        self._benchmark_root = benchmark_root
        self._checker_binary = checker_binary

    def benchmark_dir(self) -> str:
        """Directory of this mode's benchmark files. Default `<root>/<name>`."""
        return os.path.join(self._benchmark_root, self.name)

    def checker_binary_path(self) -> str:
        return self._checker_binary

    def is_benchmark_file(self, path: str) -> bool:
        """Distinguish a benchmark from a dependency .tla copy.

        Both generators name benchmarks `SourceFile_TheoremName.tla`
        and most dependencies as plain module names, so an underscore in the
        module name is a necessary signal. But it is NOT sufficient: a shared
        model layer can itself carry an underscore — either because the source
        module name does (e.g. `ZkV3_7_0.tla`) or by the `_proof.tla` convention
        (e.g. `EWD840_proof.tla`, which other tasks EXTEND but which states no
        goal of its own). A real benchmark always carries a top-level proof goal
        (THEOREM/LEMMA/...), while a model/dependency layer does not. Require
        BOTH so the model file is treated as a dependency, not run as a task.
        """
        name = os.path.splitext(os.path.basename(path))[0]
        if "_" not in name:
            return False
        try:
            with open(path) as f:
                text = f.read()
        except OSError:
            return False
        return _TOP_LEVEL_GOAL.search(text) is not None

    def get_benchmark_files(self, filter_pattern: str | None = None) -> list[str]:
        files = sorted(glob.glob(os.path.join(self.benchmark_dir(), "**", "*.tla"), recursive=True))
        files = [f for f in files if self.is_benchmark_file(f)]
        if filter_pattern:
            patterns = [p.strip() for p in filter_pattern.split(",")]
            files = [f for f in files if any(p in f for p in patterns)]
        return files

    def get_dependencies(self, benchmark_path: str) -> list[str]:
        """Sibling .tla files the agent's workspace needs alongside the target.

        Two sources, unioned:
          1. Every sibling that is NOT itself a benchmark task — the shared model
             / dependency layers (a file with no top-level goal).
          2. The EXTENDS / INSTANCE closure of the target. This pulls in a shared
             base module even when it is ALSO a benchmark task in its own right
             (e.g. ``CRDT_proof.tla``, which the per-theorem CRDT tasks EXTEND but
             which itself carries a goal). ``is_benchmark_file`` would exclude such
             a module from (1), leaving the workspace unable to even parse the
             target — so we follow the actual dependency edges here.
        """
        bench_dir = os.path.dirname(benchmark_path)
        target_abs = os.path.abspath(benchmark_path)
        target_name = os.path.splitext(os.path.basename(benchmark_path))[0]

        siblings = {os.path.splitext(os.path.basename(f))[0]: os.path.abspath(f) for f in
                    glob.glob(os.path.join(bench_dir, "*.tla"))}

        deps: set[str] = set()
        # (1) non-benchmark sibling modules — the shared/model layers.
        for path in siblings.values():
            if path != target_abs and not self.is_benchmark_file(path):
                deps.add(path)

        # (2) EXTENDS / INSTANCE closure from the target, across siblings only.
        seen = {target_name}
        stack = [target_abs]
        goal_bearing: list[str] = []
        while stack:
            cur = stack.pop()
            try:
                with open(cur, encoding="utf-8", errors="ignore") as fh:
                    refs = _referenced_modules(fh.read())
            except OSError:
                continue
            for ref in refs:
                if ref in seen:
                    continue
                seen.add(ref)
                sp = siblings.get(ref)
                if sp and sp != target_abs:
                    # A goal-bearing module reached only via the closure means a
                    # task EXTENDS another task — copying it is required to parse,
                    # but it usually signals a benchmark generation bug (e.g. a
                    # shared base left carrying stray goals). Warn, don't hide it.
                    if sp not in deps and self.is_benchmark_file(sp):
                        goal_bearing.append(os.path.basename(sp))
                    deps.add(sp)
                    stack.append(sp)

        if goal_bearing:
            print(
                f"WARNING [{os.path.basename(benchmark_path)}]: dependency closure pulled in "
                f"goal-bearing module(s) {goal_bearing} — a task extending another task may "
                f"indicate a benchmark generation bug.",
                file=sys.stderr,
            )
        return sorted(deps)

    def prompt_template_path(self) -> str:
        prompts_dir = os.path.join(
            os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
            "prompts",
        )
        return os.path.join(prompts_dir, f"{self.name}.txt")

    def build_prompt(self, benchmark_basename: str, tlapm_path: str, tlapm_lib: str) -> str:
        with open(self.prompt_template_path()) as f:
            template = f.read()
        return template.format(
            benchmark_basename=benchmark_basename,
            tlapm_path=tlapm_path,
            tlapm_lib=tlapm_lib,
        )

    def checker_command(
        self, workspace: str, benchmark_basename: str, output_path: str, timeout: int, benchmark_dir: str | None = None
    ) -> list[str]:
        cmd = [
            self._checker_binary,
            os.path.join(workspace, benchmark_basename),
            "--no-container",
            "--mode",
            self.name,
            "--output",
            output_path,
            "--timeout",
            str(timeout),
        ]
        # Grading passes the canonical read-only module dir so the semantic
        # engine's provenance is tamper-proof (the agent's own self-check falls
        # back to git-root reconstruction inside its workspace).
        if benchmark_dir:
            cmd += ["--benchmark-dir", benchmark_dir]
        return cmd
