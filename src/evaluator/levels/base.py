"""Abstract base class for benchmark levels.

A `Level` is one benchmark suite — e.g. Level 1 (proof completion) or Level 2
(proof from scratch). It owns everything that varies between suites:

  - where the benchmark files live
  - how to tell a benchmark from a dependency file
  - which prompt template the agent receives
  - how to invoke the checker that grades the agent's output

The runner is level-agnostic: it asks the `Level` object for each of those.
"""

from __future__ import annotations

import glob
import os
from abc import ABC
from typing import Optional


class Level(ABC):
    name: str = ""
    level_number: int = 0
    description: str = ""

    def __init__(self, benchmark_root: str, checker_binary: str):
        """
        Args:
            benchmark_root: dir containing all level subdirs
                            (e.g. /benchmark in docker, <repo>/benchmark on host).
            checker_binary: absolute path to the check_proof binary.
        """
        if not self.name:
            raise ValueError(f"{type(self).__name__} must set `name`")
        self._benchmark_root = benchmark_root
        self._checker_binary = checker_binary

    def benchmark_dir(self) -> str:
        """Directory of this level's benchmark files. Default `<root>/<name>`."""
        return os.path.join(self._benchmark_root, self.name)

    def checker_binary_path(self) -> str:
        return self._checker_binary

    def is_benchmark_file(self, path: str) -> bool:
        """Distinguish a benchmark from a dependency .tla copy.

        Both the L1 and L2 generators name benchmarks `SourceFile_TheoremName.tla`
        and dependencies as plain module names; the underscore is the tell.
        """
        return '_' in os.path.splitext(os.path.basename(path))[0]

    def get_benchmark_files(self, filter_pattern: Optional[str] = None) -> list[str]:
        files = sorted(
            glob.glob(os.path.join(self.benchmark_dir(), '**', '*.tla'), recursive=True)
        )
        files = [f for f in files if self.is_benchmark_file(f)]
        if filter_pattern:
            patterns = [p.strip() for p in filter_pattern.split(',')]
            files = [f for f in files if any(p in f for p in patterns)]
        return files

    def get_dependencies(self, benchmark_path: str) -> list[str]:
        bench_dir = os.path.dirname(benchmark_path)
        deps = []
        for f in glob.glob(os.path.join(bench_dir, '*.tla')):
            if os.path.abspath(f) == os.path.abspath(benchmark_path):
                continue
            if not self.is_benchmark_file(f):
                deps.append(f)
        return deps

    def prompt_template_path(self) -> str:
        prompts_dir = os.path.join(
            os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
            'prompts',
        )
        return os.path.join(prompts_dir, f'{self.name}.txt')

    def build_prompt(self, benchmark_basename: str, tlapm_path: str, tlapm_lib: str) -> str:
        with open(self.prompt_template_path(), 'r') as f:
            template = f.read()
        return template.format(
            benchmark_basename=benchmark_basename,
            tlapm_path=tlapm_path,
            tlapm_lib=tlapm_lib,
        )

    def checker_command(self, workspace: str, benchmark_basename: str,
                        output_path: str, timeout: int,
                        benchmark_dir: str | None = None) -> list[str]:
        cmd = [
            self._checker_binary,
            os.path.join(workspace, benchmark_basename),
            '--level', str(self.level_number),
            '--output', output_path,
            '--timeout', str(timeout),
        ]
        # Grading passes the canonical read-only module dir so the semantic
        # engine's provenance is tamper-proof (the agent's own self-check falls
        # back to git-root reconstruction inside its workspace).
        if benchmark_dir:
            cmd += ['--benchmark-dir', benchmark_dir]
        return cmd
