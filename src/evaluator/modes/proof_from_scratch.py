"""proof-from-scratch — proof from scratch.

The benchmark file keeps the model (definitions, constants, variables,
assumptions) and only the target theorem's statement, with `PROOF OBVIOUS`
in place of its body. All other theorems and lemmas are stripped. The agent
must invent the proof structure — including any helper lemmas — from scratch.

Because the agent is allowed to add new lemmas above the target theorem,
the strict proof-completion preamble-integrity check does not apply here.
"""

from functools import cached_property
from pathlib import Path

from common.proof_from_scratch_contract import TaskBoundary, load_proof_from_scratch_manifest

from .base import Mode


class ProofFromScratch(Mode):
    name = "proof-from-scratch"
    description = "Proof from scratch — agent invents the proof structure"
    read_only_dependencies = True
    canonical_replay_required = True
    requires_workspace_tools = True

    @cached_property
    def _boundaries(self) -> tuple[TaskBoundary, ...]:
        # Keep a pickleable tuple on the mode: WorkItem sends this object to
        # worker processes when the evaluator runs with --jobs > 1.
        return tuple(load_proof_from_scratch_manifest(Path(self.benchmark_dir())).values())

    @cached_property
    def _boundaries_by_path(self) -> dict[Path, TaskBoundary]:
        return {boundary.task_path: boundary for boundary in self._boundaries}

    def is_benchmark_file(self, path: str) -> bool:
        """Return whether ``path`` is a task declared by the manifest."""

        try:
            resolved = Path(path).resolve(strict=True)
        except (OSError, RuntimeError):
            return False
        return resolved in self._boundaries_by_path

    def get_benchmark_files(self, filter_pattern: str | None = None) -> list[str]:
        """Discover tasks exclusively from sorted manifest entries."""

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
        """Return only the exact context declared for a manifest task."""

        try:
            resolved = Path(benchmark_path).resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            raise ValueError(f"proof-from-scratch benchmark does not exist: {benchmark_path}") from exc

        boundary = self._boundaries_by_path.get(resolved)
        if boundary is None:
            raise ValueError(
                f"proof-from-scratch benchmark is not declared in {self.benchmark_dir()}/manifest.json: "
                f"{benchmark_path}"
            )
        return [str(path) for path in boundary.context_paths]

    def build_one_shot_prompt(self, benchmark_path: str, dependencies: list[str]) -> str:
        del benchmark_path, dependencies
        raise ValueError("proof-from-scratch requires a backend with workspace tools")
