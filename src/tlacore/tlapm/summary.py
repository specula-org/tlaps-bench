"""Run ``tlapm --summary`` and parse its obligation accounting.

``--summary`` is tlapm's own ground-truth on what got proved vs admitted. A
theorem with a bare QED / missing step shows up as an "incomplete proof of
theorem at line N" section with ``missing_proofs_count > 0`` and the line of
each missing step. A bare/OMITTED theorem contributes 0 obligations. This is
far more robust than reading source text, and it sees inside structured proofs
(bare QED) which a top-level proof-node check would miss.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .invoke import run_killgroup
from .locate import find_community_lib, resolve


@dataclass
class IncompleteProof:
    theorem_line: int
    missing_count: int
    missing_lines: list[int] = field(default_factory=list)


@dataclass
class Summary:
    obligations_count: int = 0
    missing_proofs_count: int = 0
    incomplete: list[IncompleteProof] = field(default_factory=list)
    raw: str = ""

    def incomplete_lines(self) -> set[int]:
        """The set of theorem lines that have an incomplete (admitted) proof."""
        return {ip.theorem_line for ip in self.incomplete}


_OBL = re.compile(r"obligations_count\s*=\s*(\d+)")
_MISS_TOP = re.compile(r"^\s*missing_proofs_count\s*=\s*(\d+)", re.MULTILINE)
_SECTION = re.compile(r"----\s+incomplete proof of theorem at line (\d+),\s*character \d+\s*----")
_MISS_LOC = re.compile(r"missing_proof_\d+\s+at\s+line\s+(\d+)")


def parse_summary(output: str) -> Summary:
    """Parse ``tlapm --summary`` text into a :class:`Summary`."""
    s = Summary(raw=output)
    m = _OBL.search(output)
    if m:
        s.obligations_count = int(m.group(1))
    # The first top-level missing_proofs_count is the module total (if present).
    top = _MISS_TOP.search(output)
    if top:
        s.missing_proofs_count = int(top.group(1))

    # Split into per-theorem incomplete sections.
    matches = list(_SECTION.finditer(output))
    for i, mt in enumerate(matches):
        start = mt.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(output)
        section = output[start:end]
        cnt_m = re.search(r"missing_proofs_count\s*=\s*(\d+)", section)
        cnt = int(cnt_m.group(1)) if cnt_m else 0
        locs = [int(x) for x in _MISS_LOC.findall(section)]
        s.incomplete.append(IncompleteProof(int(mt.group(1)), cnt, locs))
    return s


def run_summary(
    tla_path: str, cwd: str, *, tlapm: str | None = None, tlapm_lib: str | None = None, timeout: float = 600
) -> Summary:
    """Run ``tlapm --summary`` on ``tla_path`` and return the parsed summary."""
    tlapm, tlapm_lib = resolve(tlapm, tlapm_lib)
    cmd = [tlapm, "--summary", "-I", tlapm_lib]
    community = find_community_lib()
    if community:
        cmd += ["-I", community]
    cmd.append(tla_path)
    out, err, _ = run_killgroup(cmd, timeout, cwd)
    return parse_summary(out + err)
