#!/usr/bin/env python3
"""Annotate Proof Completion manifest entries with reference_proof_steps."""

from __future__ import annotations

import json
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from dataset.proof_completion.reference_steps import (  # noqa: E402
    find_reference_proof_steps,
    source_index,
)

SUITE = PROJECT_ROOT / "benchmark" / "proof-completion"
MANIFEST = SUITE / "manifest.json"
SOURCE = PROJECT_ROOT / "source"


def main() -> int:
    raw = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise SystemExit(f"unexpected manifest root: {type(raw)}")

    index = source_index(SOURCE)
    updated: dict[str, dict] = {}
    missing = 0
    for task_key, entry in raw.items():
        if not isinstance(entry, dict):
            raise SystemExit(f"bad entry for {task_key!r}")
        steps = find_reference_proof_steps(
            task_key,
            suite_root=SUITE,
            source_root=SOURCE,
            indexed_sources=index,
        )
        if steps is None:
            missing += 1
        updated[task_key] = {
            "spec_id": entry["spec_id"],
            "context": entry["context"],
            "reference_proof_steps": steps,
        }

    MANIFEST.write_text(
        json.dumps(dict(sorted(updated.items())), indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(f"Annotated {len(updated)} tasks ({missing} with null reference_proof_steps)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
