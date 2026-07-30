"""Compatibility facade for the proof-from-scratch task contract."""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path

from common.task_contract import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    EDITABLE_REGION_MARKERS,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
    EditableRegionError,
    EditableRegions,
    ManifestError,
    TaskBoundary,
    TaskContractError,
    parse_editable_regions,
)
from common.task_contract import load_task_manifest as _load_task_manifest

ProofFromScratchContractError = TaskContractError


def load_proof_from_scratch_manifest(suite_root: Path) -> Mapping[str, TaskBoundary]:
    """Load the strict proof-from-scratch manifest without a fallback."""

    return _load_task_manifest(
        suite_root,
        suite_name="proof-from-scratch",
        parse_task_regions=parse_editable_regions,
    )


__all__ = [
    "BEGIN_AGENT_HELPERS",
    "BEGIN_AGENT_PROOF",
    "EDITABLE_REGION_MARKERS",
    "END_AGENT_HELPERS",
    "END_AGENT_PROOF",
    "EditableRegionError",
    "EditableRegions",
    "ManifestError",
    "ProofFromScratchContractError",
    "TaskBoundary",
    "load_proof_from_scratch_manifest",
    "parse_editable_regions",
]
