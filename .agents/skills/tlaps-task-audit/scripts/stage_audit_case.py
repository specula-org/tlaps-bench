"""Stage exact canonical and candidate directories for one TLAPS task audit."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1


class StageError(ValueError):
    """Report an invalid staging request without a traceback."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_manifest(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise StageError(f"Cannot read manifest {path}: {error}") from error
    if not isinstance(data, dict):
        raise StageError(f"Manifest {path} is not a JSON object.")
    return data


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=".", help="Repository root. Default: current directory.")
    parser.add_argument("--mode", default="proof-completion", help="Benchmark mode directory name.")
    parser.add_argument("--task", required=True, help="Exact mode-relative task ID.")
    parser.add_argument("--output-dir", required=True, help="New or empty audit-case directory.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        repo = Path(args.repo).resolve()
        mode_dir = repo / "benchmark" / args.mode
        manifest_path = mode_dir / "manifest.json"
        manifest = load_manifest(manifest_path)
        if args.task not in manifest:
            raise StageError(f"Unknown task ID: {args.task}")

        entry = manifest[args.task]
        if not isinstance(entry, dict):
            raise StageError(f"Manifest entry for {args.task} is not an object.")
        contexts = entry.get("context")
        if not isinstance(contexts, list) or not contexts or not all(isinstance(item, str) for item in contexts):
            raise StageError(f"Manifest entry for {args.task} has no valid context list.")

        source_paths = [mode_dir / args.task, *(mode_dir / item for item in contexts)]
        missing = [str(path) for path in source_paths if not path.is_file()]
        if missing:
            raise StageError(f"Missing task context files: {', '.join(missing)}")

        basenames = [path.name for path in source_paths]
        duplicates = sorted({name for name in basenames if basenames.count(name) > 1})
        if duplicates:
            raise StageError(f"Context file-name collision: {', '.join(duplicates)}")

        output_dir = Path(args.output_dir).resolve()
        if output_dir.exists() and any(output_dir.iterdir()):
            raise StageError(f"Output directory is not empty: {output_dir}")
        output_dir.mkdir(parents=True, exist_ok=True)
        canonical_dir = output_dir / "canonical"
        candidate_dir = output_dir / "candidate"
        canonical_dir.mkdir()
        candidate_dir.mkdir()

        files: list[dict[str, Any]] = []
        for index, source_path in enumerate(source_paths):
            canonical_path = canonical_dir / source_path.name
            candidate_path = candidate_dir / source_path.name
            shutil.copy2(source_path, canonical_path)
            shutil.copy2(source_path, candidate_path)
            files.append(
                {
                    "role": "target" if index == 0 else "context",
                    "task_relative_path": source_path.relative_to(mode_dir).as_posix(),
                    "staged_name": source_path.name,
                    "sha256": sha256_file(source_path),
                }
            )

        metadata = {
            "schema_version": SCHEMA_VERSION,
            "mode": args.mode,
            "task_id": args.task,
            "target_file": source_paths[0].name,
            "canonical_dir": str(canonical_dir),
            "candidate_dir": str(candidate_dir),
            "community_lib": str(repo / "lib" / "community"),
            "files": files,
        }
        metadata_path = output_dir / "case.json"
        metadata_path.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")

        print(f"Staged {len(files)} files for {args.task}")
        print(f"Edit only: {candidate_dir / source_paths[0].name}")
        print(f"Canonical directory: {canonical_dir}")
        print(f"Metadata: {metadata_path}")
        return 0
    except (OSError, StageError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
