"""Build a stable inventory for a TLAPS Bench task audit."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1
BEGIN_MARKER = r"\* BEGIN AGENT PROOF"
END_MARKER = r"\* END AGENT PROOF"


class AuditInputError(ValueError):
    """Report an invalid audit input without a traceback."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def repo_relative(path: Path, repo: Path) -> str:
    return path.resolve().relative_to(repo).as_posix()


def git_commit(repo: Path) -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise AuditInputError(f"Cannot read the Git commit: {result.stderr.strip()}")
    return result.stdout.strip()


def load_json_object(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise AuditInputError(f"Cannot read JSON file {path}: {error}") from error
    if not isinstance(data, dict):
        raise AuditInputError(f"Expected a JSON object in {path}")
    return data


def resolve_task_list(
    value: str, repo: Path, mode_dir: Path, manifest: dict[str, Any]
) -> tuple[list[str], str, str | None]:
    if value == "full":
        return sorted(manifest), "manifest:full", None

    raw_path = Path(value)
    candidates = [raw_path] if raw_path.is_absolute() else [repo / raw_path, Path.cwd() / raw_path]
    candidates.append(mode_dir / f"{value}.txt")

    list_path = next((path.resolve() for path in candidates if path.is_file()), None)
    if list_path is None:
        raise AuditInputError(f"Unknown task list {value!r}. Pass 'full', a registered name, or a file path.")

    lines = list_path.read_text(encoding="utf-8").splitlines()
    task_ids = [line.strip() for line in lines if line.strip() and not line.lstrip().startswith("#")]
    try:
        source = repo_relative(list_path, repo)
    except ValueError:
        source = str(list_path)
    return task_ids, source, sha256_file(list_path)


def validate_task_ids(task_ids: list[str], manifest: dict[str, Any]) -> None:
    if not task_ids:
        raise AuditInputError("The selected task list is empty.")

    seen: set[str] = set()
    duplicates: list[str] = []
    for task_id in task_ids:
        if task_id in seen and task_id not in duplicates:
            duplicates.append(task_id)
        seen.add(task_id)
    if duplicates:
        raise AuditInputError(f"Duplicate task IDs: {', '.join(duplicates)}")

    unknown = [task_id for task_id in task_ids if task_id not in manifest]
    if unknown:
        raise AuditInputError(f"Unknown task IDs: {', '.join(unknown)}")


def required_file(path: Path, label: str) -> None:
    if not path.is_file():
        raise AuditInputError(f"Missing {label}: {path}")


def build_task_record(
    *,
    ordinal: int,
    batch_size: int,
    task_id: str,
    entry: Any,
    repo: Path,
    mode_dir: Path,
) -> dict[str, Any]:
    if not isinstance(entry, dict):
        raise AuditInputError(f"Manifest entry for {task_id} is not an object.")

    spec_id = entry.get("spec_id")
    contexts = entry.get("context")
    if not isinstance(spec_id, str) or not spec_id:
        raise AuditInputError(f"Manifest entry for {task_id} has no valid spec_id.")
    if not isinstance(contexts, list) or not contexts or not all(isinstance(item, str) for item in contexts):
        raise AuditInputError(f"Manifest entry for {task_id} has no valid context list.")

    target_path = mode_dir / task_id
    source_path = repo / "source" / spec_id
    required_file(target_path, "task file")
    required_file(source_path, "source file")

    target_text = target_path.read_text(encoding="utf-8")
    if target_text.count(BEGIN_MARKER) != 1 or target_text.count(END_MARKER) != 1:
        raise AuditInputError(f"Task {task_id} does not contain one complete agent-proof marker pair.")
    if target_text.index(BEGIN_MARKER) >= target_text.index(END_MARKER):
        raise AuditInputError(f"Task {task_id} has reversed agent-proof markers.")

    context_records: list[dict[str, str]] = []
    for context_id in contexts:
        context_path = mode_dir / context_id
        required_file(context_path, "context file")
        context_records.append(
            {
                "path": repo_relative(context_path, repo),
                "sha256": sha256_file(context_path),
            }
        )

    reference_steps = entry.get("reference_proof_steps")
    if reference_steps is not None and (not isinstance(reference_steps, int) or reference_steps < 0):
        raise AuditInputError(f"Manifest entry for {task_id} has invalid reference_proof_steps.")

    return {
        "ordinal": ordinal,
        "batch": ((ordinal - 1) // batch_size) + 1,
        "task_id": task_id,
        "spec_id": spec_id,
        "reference_proof_steps": reference_steps,
        "target": {
            "path": repo_relative(target_path, repo),
            "sha256": sha256_file(target_path),
        },
        "context": context_records,
        "source": {
            "path": repo_relative(source_path, repo),
            "sha256": sha256_file(source_path),
        },
    }


def write_json_atomic(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=".", help="Repository root. Default: current directory.")
    parser.add_argument("--mode", default="proof-completion", help="Benchmark mode directory name.")
    parser.add_argument(
        "--task-list",
        default="core",
        help="Registered list name, 'full', or a task-list file path.",
    )
    parser.add_argument("--batch-size", type=int, default=10, help="Tasks per audit batch.")
    parser.add_argument("--output", required=True, help="Output inventory JSON path.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        repo = Path(args.repo).resolve()
        if args.batch_size < 1:
            raise AuditInputError("--batch-size must be greater than zero.")

        mode_dir = repo / "benchmark" / args.mode
        manifest_path = mode_dir / "manifest.json"
        required_file(manifest_path, "manifest")
        manifest = load_json_object(manifest_path)

        task_ids, task_list_source, task_list_hash = resolve_task_list(args.task_list, repo, mode_dir, manifest)
        validate_task_ids(task_ids, manifest)

        tasks = [
            build_task_record(
                ordinal=ordinal,
                batch_size=args.batch_size,
                task_id=task_id,
                entry=manifest[task_id],
                repo=repo,
                mode_dir=mode_dir,
            )
            for ordinal, task_id in enumerate(task_ids, start=1)
        ]

        inventory = {
            "schema_version": SCHEMA_VERSION,
            "generated_at": datetime.now(UTC).isoformat(),
            "git_commit": git_commit(repo),
            "mode": args.mode,
            "manifest": {
                "path": repo_relative(manifest_path, repo),
                "sha256": sha256_file(manifest_path),
            },
            "task_list": {
                "source": task_list_source,
                "sha256": task_list_hash,
            },
            "batch_size": args.batch_size,
            "task_count": len(tasks),
            "batch_count": tasks[-1]["batch"],
            "tasks": tasks,
        }
        output_path = Path(args.output)
        if not output_path.is_absolute():
            output_path = repo / output_path
        write_json_atomic(output_path, inventory)
        print(f"Wrote {len(tasks)} tasks in {inventory['batch_count']} batches to {output_path}")
        return 0
    except AuditInputError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
