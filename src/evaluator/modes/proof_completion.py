"""proof-completion — fill one target proof in fixed layered scaffolding."""

from __future__ import annotations

import os
import sys
from functools import cached_property
from glob import glob
from pathlib import Path

from common.proof_completion_contract import (
    ManifestError,
    TaskBoundary,
    contains_marker_text,
    load_proof_completion_manifest,
)
from common.task_contract import EDITABLE_REGION_MARKERS, MANIFEST_FILENAME

from .base import Mode

_WARNED_LEGACY_SUITES: set[Path] = set()


class ProofCompletion(Mode):
    name = "proof-completion"
    description = "Proof completion — fill in the target theorem's proof"

    @cached_property
    def _boundaries(self) -> tuple[TaskBoundary, ...] | None:
        """Select the strict manifest contract or the guarded legacy layout."""

        suite = Path(self.benchmark_dir())
        manifest = suite / MANIFEST_FILENAME
        if manifest.exists() or manifest.is_symlink():
            return tuple(load_proof_completion_manifest(suite).values())

        if suite.is_dir():
            for path in map(Path, sorted(glob(str(suite / "**" / "*.tla"), recursive=True))):
                try:
                    source = path.read_text(encoding="utf-8")
                except (OSError, UnicodeError) as exc:
                    raise ManifestError(f"cannot inspect proof-completion task {path}: {exc}") from exc
                if contains_marker_text(source, EDITABLE_REGION_MARKERS):
                    raise ManifestError(
                        f"missing proof-completion manifest: {manifest}; marked task {path} cannot use legacy discovery"
                    )
            suite_key = suite.resolve()
            if suite_key not in _WARNED_LEGACY_SUITES:
                _WARNED_LEGACY_SUITES.add(suite_key)
                print(
                    f"WARNING: {manifest} is absent; using legacy unmarked proof-completion discovery and checking.",
                    file=sys.stderr,
                )
        return None

    @cached_property
    def _boundaries_by_path(self) -> dict[Path, TaskBoundary]:
        return {boundary.task_path: boundary for boundary in self._boundaries or ()}

    @property
    def uses_strict_contract(self) -> bool:
        return self._boundaries is not None

    @property
    def read_only_dependencies(self) -> bool:
        return self.uses_strict_contract

    @property
    def canonical_replay_required(self) -> bool:
        return self.uses_strict_contract

    def is_benchmark_file(self, path: str) -> bool:
        if not self.uses_strict_contract:
            return super().is_benchmark_file(path)
        try:
            resolved = Path(path).resolve(strict=True)
        except (OSError, RuntimeError):
            return False
        return resolved in self._boundaries_by_path

    def get_benchmark_files(self, filter_pattern: str | None = None) -> list[str]:
        if not self.uses_strict_contract:
            return super().get_benchmark_files(filter_pattern)

        boundaries = self._boundaries or ()
        if filter_pattern:
            patterns = [pattern.strip() for pattern in filter_pattern.split(",") if pattern.strip()]
            boundaries = tuple(
                boundary for boundary in boundaries if any(pattern in str(boundary.task_path) for pattern in patterns)
            )
        return [str(boundary.task_path) for boundary in boundaries]

    def get_dependencies(self, benchmark_path: str) -> list[str]:
        if not self.uses_strict_contract:
            return super().get_dependencies(benchmark_path)

        try:
            resolved = Path(benchmark_path).resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            raise ValueError(f"proof-completion benchmark does not exist: {benchmark_path}") from exc

        boundary = self._boundaries_by_path.get(resolved)
        if boundary is None:
            raise ValueError(
                f"proof-completion benchmark is not declared in {self.benchmark_dir()}/{MANIFEST_FILENAME}: "
                f"{benchmark_path}"
            )
        return [str(path) for path in boundary.context_paths]

    def prompt_template_path(self) -> str:
        if not self.uses_strict_contract:
            return super().prompt_template_path()
        prompts_dir = os.path.join(
            os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
            "prompts",
        )
        return os.path.join(prompts_dir, "proof-completion-strict.txt")

    def one_shot_prompt_template_path(self) -> str:
        if not self.uses_strict_contract:
            return super().one_shot_prompt_template_path()
        return os.path.join(os.path.dirname(self.prompt_template_path()), "proof-completion-strict-one-shot.txt")
