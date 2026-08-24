"""Trusted library modules and lightweight TLA+ module-reference discovery."""

from __future__ import annotations

import re

# Modules that tlapm resolves through its stdlib or the vendored community
# library. A benchmark manifest therefore does not need to provide these files.
STDLIB_MODULES = {
    "TLAPS",
    "Integers",
    "Naturals",
    "Sequences",
    "FiniteSets",
    "Reals",
    "Bags",
    "TLC",
    "NaturalsInduction",
    "SequenceTheorems",
    "WellFoundedInduction",
    "ProtoReals",
    "Functions",
    "SequenceOpTheorems",
    "BagsTheorems",
    "RealNumberTheorems",
    "FiniteSetTheorems",
    "FunctionTheorems",
    "Folds",
    "FiniteSetTheorems_proofs",
    "SequenceTheorems_proofs",
    "NaturalsInduction_proofs",
    "WellFoundedInduction_proofs",
    "BagsTheorems_proofs",
    "RealTime",
}

COMMUNITY_MODULES = {
    "SequencesExt",
    "SequencesExtTheorems",
    "FiniteSetsExt",
    "FunctionsExt",
    "BagsExt",
    "Relation",
    "Graphs",
    "GraphTheorems",
    "GraphsExt",
    "Combinatorics",
    "DyadicRationals",
    "Bitwise",
    "Statistics",
    "VectorClocks",
    "IOUtils",
    "CSV",
    "SVG",
    "TLCExt",
    "Json",
    "Randomization",
}

RESOLVABLE_MODULES = STDLIB_MODULES | COMMUNITY_MODULES

_MODULE_NAME = r"[A-Za-z_]\w*"
_EXTENDS_RE = re.compile(rf"\bEXTENDS\b\s+({_MODULE_NAME}(?:\s*,\s*{_MODULE_NAME})*)")
_INSTANCE_RE = re.compile(rf"\bINSTANCE\s+({_MODULE_NAME})")


def mask_comments_and_strings(source: str) -> str:
    """Replace non-code bytes with spaces while preserving physical newlines."""

    masked: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False

    while index < len(source):
        char = source[index]
        pair = source[index : index + 2]

        if in_line_comment:
            if char in "\r\n":
                in_line_comment = False
                masked.append(char)
            else:
                masked.append(" ")
            index += 1
            continue

        if block_depth:
            if pair == "(*":
                block_depth += 1
                masked.extend((" ", " "))
                index += 2
            elif pair == "*)":
                block_depth -= 1
                masked.extend((" ", " "))
                index += 2
            else:
                masked.append(char if char in "\r\n" else " ")
                index += 1
            continue

        if in_string:
            if char == "\\" and index + 1 < len(source):
                masked.extend((" ", " "))
                index += 2
            else:
                if char == '"':
                    in_string = False
                masked.append(char if char in "\r\n" else " ")
                index += 1
            continue

        if pair == r"\*":
            in_line_comment = True
            masked.extend((" ", " "))
            index += 2
        elif pair == "(*":
            block_depth = 1
            masked.extend((" ", " "))
            index += 2
        elif char == '"':
            in_string = True
            masked.append(" ")
            index += 1
        else:
            masked.append(char)
            index += 1

    return "".join(masked)


def referenced_modules(source: str) -> set[str]:
    """Return module names referenced by code-level ``EXTENDS`` or ``INSTANCE``."""

    code = mask_comments_and_strings(source)
    names: set[str] = set()
    for match in _EXTENDS_RE.finditer(code):
        names.update(name.strip() for name in match.group(1).split(","))
    names.update(match.group(1) for match in _INSTANCE_RE.finditer(code))
    return names
