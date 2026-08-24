"""proof-completion — fill one target proof in fixed layered scaffolding."""

from __future__ import annotations

import os
from functools import cached_property
from pathlib import Path

from common.proof_completion_contract import TaskBoundary, load_proof_completion_manifest
from common.task_contract import MANIFEST_FILENAME

from .base import Mode


class ProofCompletion(Mode):
    name = "proof-completion"
    description = "Proof completion — fill in the target theorem's proof"
    read_only_dependencies = True
    canonical_replay_required = True

    @cached_property
    def _boundaries(self) -> tuple[TaskBoundary, ...]:
        """Load the required manifest-backed proof-completion contract."""

        return tuple(load_proof_completion_manifest(Path(self.benchmark_dir())).values())

    @cached_property
    def _boundaries_by_path(self) -> dict[Path, TaskBoundary]:
        return {boundary.task_path: boundary for boundary in self._boundaries}

    def is_benchmark_file(self, path: str) -> bool:
        try:
            resolved = Path(path).resolve(strict=True)
        except (OSError, RuntimeError):
            return False
        return resolved in self._boundaries_by_path

    def get_benchmark_files(self, filter_pattern: str | None = None) -> list[str]:
        boundaries = self._boundaries
        if filter_pattern:
            patterns = [pattern.strip() for pattern in filter_pattern.split(",") if pattern.strip()]
            boundaries = tuple(
                boundary for boundary in boundaries if any(pattern in str(boundary.task_path) for pattern in patterns)
            )
        return [str(boundary.task_path) for boundary in boundaries]

    def specification_ids(self) -> dict[str, str]:
        return {boundary.task_key: boundary.spec_id for boundary in self._boundaries}

    def get_dependencies(self, benchmark_path: str) -> list[str]:
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
        prompts_dir = os.path.join(
            os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
            "prompts",
        )
        return os.path.join(prompts_dir, "proof-completion-strict.txt")

    def one_shot_prompt_template_path(self) -> str:
        return os.path.join(os.path.dirname(self.prompt_template_path()), "proof-completion-strict-one-shot.txt")
