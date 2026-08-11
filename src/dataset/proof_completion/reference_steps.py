"""Count reference-proof steps for Proof Completion tasks."""

from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path

STEP_LINE_RE = re.compile(r"^[ \t]*<(\d+)")
_THEOREM_HEADER_RE = re.compile(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(\w+)\s*==")


def strip_block_and_line_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    in_block = False
    while i < n:
        if not in_block and text.startswith("(*", i):
            in_block = True
            i += 2
            continue
        if in_block:
            if text.startswith("*)", i):
                in_block = False
                i += 2
            else:
                i += 1
            continue
        if text.startswith("\\*", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def count_reference_proof_steps(proof_lines: list[str]) -> int:
    clean = strip_block_and_line_comments("\n".join(proof_lines))
    return sum(1 for line in clean.splitlines() if STEP_LINE_RE.match(line))


def reference_proof_steps_for_name(source_lines: list[str], theorem_name: str) -> int | None:
    from dataset.proof_completion.generate import get_theorem_proof_lines, parse_theorems

    for thm in parse_theorems(source_lines):
        if thm.name == theorem_name and thm.has_proof:
            proof_lines = get_theorem_proof_lines(source_lines, thm)
            while proof_lines and not proof_lines[-1].strip():
                proof_lines.pop()
            while proof_lines:
                trailing = proof_lines[-1].strip()
                if not trailing or trailing.startswith("(*") or trailing.startswith("\\*"):
                    proof_lines.pop()
                    continue
                break
            return count_reference_proof_steps(proof_lines)
    return None


def target_theorem_name(task_path: Path) -> str | None:
    try:
        lines = task_path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError):
        return None
    for line in reversed(lines):
        match = _THEOREM_HEADER_RE.match(line.strip())
        if match:
            return match.group(2)
    return None


def source_index(source_root: Path) -> dict[str, list[Path]]:
    index: dict[str, list[Path]] = defaultdict(list)
    for path in source_root.rglob("*.tla"):
        try:
            relative = path.relative_to(source_root)
        except ValueError:
            continue
        if relative.parts:
            index[relative.parts[0]].append(path)
    return index


def find_reference_proof_steps(
    task_key: str,
    *,
    suite_root: Path,
    source_root: Path,
    indexed_sources: dict[str, list[Path]] | None = None,
) -> int | None:
    module_dir = task_key.split("/", 1)[0]
    name_no_ext = Path(task_key).stem
    theorem = target_theorem_name(suite_root / task_key)
    if not theorem:
        return None

    index = indexed_sources if indexed_sources is not None else source_index(source_root)
    candidates: list[Path] = []
    for path in index.get(module_dir, []):
        if name_no_ext.startswith(path.stem + "_"):
            candidates.insert(0, path)
        else:
            candidates.append(path)

    for source_path in candidates:
        try:
            source_lines = source_path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeError):
            continue
        steps = reference_proof_steps_for_name(source_lines, theorem)
        if steps is not None:
            return steps
    return None
