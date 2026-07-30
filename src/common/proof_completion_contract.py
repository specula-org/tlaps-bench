"""Strict contract for layered proof-completion tasks."""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path

from common.task_contract import (
    BEGIN_AGENT_PROOF,
    EDITABLE_REGION_MARKERS,
    END_AGENT_PROOF,
    EditableRegionError,
    ManifestError,
    ProofRegion,
    TaskBoundary,
    TaskContractError,
    contains_marker_text,
    has_marker_line,
    load_task_manifest,
    parse_proof_region,
)

ProofCompletionContractError = TaskContractError


def parse_proof_completion_region(source: str) -> ProofRegion:
    """Parse the sole editable region allowed in a proof-completion target."""

    helper_markers = EDITABLE_REGION_MARKERS[:2]
    if has_marker_line(source, helper_markers):
        raise EditableRegionError("proof-completion tasks must not contain an AGENT HELPERS region")
    return parse_proof_region(source)


def load_proof_completion_manifest(suite_root: Path) -> Mapping[str, TaskBoundary]:
    """Load the strict proof-completion manifest without a fallback."""

    return load_task_manifest(
        suite_root,
        suite_name="proof-completion",
        parse_task_regions=parse_proof_completion_region,
    )


__all__ = [
    "BEGIN_AGENT_PROOF",
    "END_AGENT_PROOF",
    "EditableRegionError",
    "ManifestError",
    "ProofCompletionContractError",
    "ProofRegion",
    "TaskBoundary",
    "contains_marker_text",
    "has_marker_line",
    "load_proof_completion_manifest",
    "parse_proof_completion_region",
    "parse_proof_region",
]
