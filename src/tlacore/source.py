"""TLA+ source-text utilities shared across the toolchain.

These operate on raw text and are deliberately *not* the basis for cheat
detection (SANY is). They cover the cases where text manipulation is genuinely
needed: stripping comments for display/diffing, and slicing a source range by
SANY-reported location.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .model import Loc

_BLOCK_COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
_LINE_COMMENT = re.compile(r"\\\*.*$", re.MULTILINE)


def strip_comments(text: str) -> str:
    """Remove block comments ``(* ... *)`` and line comments ``\\* ...``.

    Note: this is a textual approximation (it does not skip over string
    literals). Fine for display and rough diffs; never use it to decide cheating.
    """
    text = _BLOCK_COMMENT.sub("", text)
    text = _LINE_COMMENT.sub("", text)
    return text


def slice_loc(source: str, loc: Loc) -> str:
    """Extract the substring of ``source`` covered by a SANY ``Loc`` (1-based)."""
    lines = source.splitlines()
    if not loc or loc.line_start < 1 or loc.line_start > len(lines):
        return ""
    if loc.line_start == loc.line_end:
        return lines[loc.line_start - 1][loc.column_start - 1 : loc.column_end]
    out = [lines[loc.line_start - 1][loc.column_start - 1 :]]
    out.extend(lines[loc.line_start : loc.line_end - 1])
    out.append(lines[loc.line_end - 1][: loc.column_end])
    return "\n".join(out)
