#!/usr/bin/env python3
"""
Shared cheating detection for TLAPS benchmarks.

Used by both check_proof.py (AI agent feedback) and validate_benchmarks.py (batch validation).
"""

import re
from dataclasses import dataclass


@dataclass
class CheatingIssue:
    kind: str  # e.g. "PROOF_OMITTED", "EXTRA_AXIOM", "STATEMENT_MODIFIED"
    description: str
    line: int | None = None


def strip_comments(text: str) -> str:
    """Remove both block comments (* ... *) and line comments \\* ..."""
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.DOTALL)
    text = re.sub(r"\\\*.*$", "", text, flags=re.MULTILINE)
    return text


def detect_proof_omitted(proof_text: str) -> list[CheatingIssue]:
    """Check for PROOF OMITTED or bare OMITTED in proof text."""
    issues = []
    if re.search(r"\bPROOF\s+OMITTED\b", proof_text):
        issues.append(CheatingIssue("PROOF_OMITTED", "Proof uses PROOF OMITTED to skip obligations"))

    clean = strip_comments(proof_text)
    for i, line in enumerate(clean.split("\n")):
        if line.strip() == "OMITTED":
            issues.append(CheatingIssue("OMITTED", "Bare OMITTED used as proof step", line=i + 1))
    return issues


def detect_extra_axioms(original_content: str, current_content: str) -> list[CheatingIssue]:
    """Check if new AXIOM/ASSUME/ASSUMPTION declarations were added."""
    issues = []
    orig_axioms = set(re.findall(r"^(AXIOM|ASSUME|ASSUMPTION)\b.*", original_content, re.MULTILINE))
    new_axioms = set(re.findall(r"^(AXIOM|ASSUME|ASSUMPTION)\b.*", current_content, re.MULTILINE))

    for ax in new_axioms - orig_axioms:
        keyword = ax.split()[0]
        issues.append(CheatingIssue("EXTRA_AXIOM", f"New {keyword} declaration added — bypasses proof obligation"))
    return issues


def detect_preamble_modification(
    original_lines: list[str], current_lines: list[str], proof_obvious_line: int
) -> list[CheatingIssue]:
    """Check that everything before PROOF OBVIOUS is unchanged."""
    issues = []
    for i in range(proof_obvious_line):
        if i >= len(current_lines):
            issues.append(
                CheatingIssue(
                    "PREAMBLE_MODIFIED",
                    f"Line {i + 1} deleted from preamble (was: {original_lines[i].rstrip()})",
                    line=i + 1,
                )
            )
        elif original_lines[i] != current_lines[i]:
            issues.append(
                CheatingIssue(
                    "PREAMBLE_MODIFIED",
                    f"Preamble modified at line {i + 1}: was [{original_lines[i].rstrip()}], now [{current_lines[i].rstrip()}]",
                    line=i + 1,
                )
            )
    return issues


def detect_zero_total_obligations(tlapm_output: str) -> list[CheatingIssue]:
    """Check if tlapm passed with 0 total obligations — nothing was actually proved."""
    issues = []
    # Find the LAST obligation count (the target file's, not TLAPS.tla's)
    all_matches = re.findall(r"(\d+)\s+obligation", tlapm_output)
    if all_matches and int(all_matches[-1]) == 0:
        issues.append(CheatingIssue("ZERO_OBLIGATION", "tlapm passed with 0 obligations — nothing was actually proved"))
    return issues


def detect_empty_proof(proof_text_clean: str) -> list[CheatingIssue]:
    """Check for empty PROOF blocks: 'PROOF' followed by nothing before
    module end (====) or end of file.

    This catches the cheat where a bare PROOF keyword produces 0 obligations.
    A PROOF followed by <n> steps or QED is a normal hierarchical proof.
    """
    issues = []
    lines = proof_text_clean.split("\n")
    for i, line in enumerate(lines):
        stripped = line.strip()
        # Match a line that is exactly "PROOF" (not PROOF OBVIOUS, PROOF OMITTED, PROOF BY ...)
        if stripped == "PROOF":
            # Look at what follows: skip blank lines
            is_empty = True
            for j in range(i + 1, len(lines)):
                next_stripped = lines[j].strip()
                if not next_stripped:
                    continue
                # Only empty if next non-blank line is ==== (module end)
                is_empty = bool(re.match(r"^={3,}", next_stripped))
                break
            # Also empty if nothing follows at all (EOF)
            if is_empty:
                issues.append(
                    CheatingIssue(
                        "EMPTY_PROOF",
                        f"Empty PROOF keyword at line {i + 1} — produces 0 obligations for this step",
                        line=i + 1,
                    )
                )
    return issues


def detect_statement_modification(
    original_content: str, current_content: str, parse_theorems_fn
) -> list[CheatingIssue]:
    """Check if the target theorem statement was modified."""
    issues = []

    def get_last_stmt(content):
        lines = content.split("\n")
        thms = parse_theorems_fn(lines)
        if thms:
            last = thms[-1]
            return "\n".join(lines[last.statement_start : last.statement_end + 1]).strip()
        return None

    orig_stmt = get_last_stmt(original_content)
    new_stmt = get_last_stmt(current_content)
    if orig_stmt and new_stmt and orig_stmt != new_stmt:
        issues.append(CheatingIssue("STATEMENT_MODIFIED", "Theorem statement was modified from the original"))
    return issues


def detect_missing_proof(
    original_lines: list[str], current_lines: list[str], proof_obvious_line: int
) -> list[CheatingIssue]:
    """Check that the target theorem still has a PROOF block in the current file.

    Catches the cheat where PROOF OBVIOUS is simply deleted (leaving a bare
    theorem declaration that generates 0 obligations) while a fake theorem
    with a trivial proof is added to produce non-zero obligation counts.
    """
    issues = []
    # The PROOF OBVIOUS line in the original marks where the proof should be.
    # In the current file, from that line onward, the FIRST PROOF keyword should
    # appear BEFORE any new THEOREM/LEMMA/COROLLARY/PROPOSITION declaration.
    # If a new theorem appears first, it means the target theorem was left as a
    # bare declaration (0 obligations) and a fake theorem was added.
    clean = strip_comments("\n".join(current_lines[proof_obvious_line:]))
    found_proof = False
    for line in clean.split("\n"):
        stripped = line.strip()
        if not stripped:
            continue
        # Check if we hit a PROOF keyword
        if re.match(r"^PROOF\b", stripped) or re.search(r"\bPROOF\b", stripped):
            found_proof = True
            break
        # Check if we hit proof steps directly (valid TLAPS syntax without explicit PROOF keyword)
        if re.match(r"^<\d+>", stripped):
            found_proof = True
            break
        # Check if we hit a new theorem declaration before finding PROOF
        if re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\b", stripped):
            break
        # Check for module end
        if re.match(r"^={3,}", stripped):
            break
    if not found_proof:
        issues.append(
            CheatingIssue(
                "MISSING_PROOF",
                "Target theorem has no PROOF block — bare declaration generates 0 obligations",
                line=proof_obvious_line + 1,
            )
        )
    return issues


def detect_missing_proofs_summary(summary_output: str, target_theorem_line: int | None = None) -> list[CheatingIssue]:
    """Check tlapm --summary output for missing proofs in the target theorem.

    tlapm treats a bare QED (without BY/OBVIOUS) as an implicit omission,
    generating 0 obligations for that step. The --summary flag reports these
    as missing_proofs_count > 0.

    We only check the section matching the target theorem (by line number),
    because earlier theorems may have bare declarations (source artifacts)
    that also produce missing_proofs_count — those are not AI cheating.

    If target_theorem_line is not provided, we skip detection (cannot
    distinguish scaffolding from target).

    This catches cheating vectors such as:
    - Bare QED steps (no BY/OBVIOUS)
    - Any proof step left without justification in the target theorem
    """
    issues = []
    if target_theorem_line is None:
        return issues

    # Find the section for the target theorem by line number
    # Format: "---- incomplete proof of theorem at line N, character M ----"
    pattern = rf"----\s+incomplete proof of theorem at line {target_theorem_line}\b"
    m = re.search(pattern, summary_output)
    if not m:
        return issues  # target theorem not in incomplete list — good

    # Extract this section (until next "----" section or "====")
    start = m.end()
    end_m = re.search(r"\n\s*====", summary_output[start:])
    section = summary_output[start : start + end_m.start()] if end_m else summary_output[start:]

    m2 = re.search(r"missing_proofs_count\s*=\s*(\d+)", section)
    if m2 and int(m2.group(1)) > 0:
        count = int(m2.group(1))
        locations = re.findall(r"missing_proof_\d+\s+at\s+line\s+(\d+)", section)
        loc_str = f" (at line(s) {', '.join(locations)})" if locations else ""
        issues.append(
            CheatingIssue(
                "MISSING_PROOF_STEPS",
                f"tlapm --summary reports {count} missing proof(s){loc_str} in target theorem — proof is incomplete",
            )
        )
    return issues


def detect_dependency_modification(dep_files: dict[str, tuple[str, str]]) -> list[CheatingIssue]:
    """Check if dependency .tla files were modified.

    Args:
        dep_files: dict of {filename: (original_content, current_content)}
    """
    issues = []
    for filename, (original, current) in dep_files.items():
        if original != current:
            issues.append(
                CheatingIssue("DEPENDENCY_MODIFIED", f"Dependency file {filename} was modified — not allowed")
            )
    return issues


def detect_cheating_full(
    proof_text: str,
    original_content: str,
    current_content: str,
    tlapm_output: str = "",
    tlapm_passed: bool = False,
    parse_theorems_fn=None,
    dep_files: dict[str, tuple[str, str]] | None = None,
) -> list[CheatingIssue]:
    """Run all cheating checks. This is the main entry point.

    Args:
        proof_text: The proof section text (after PROOF OBVIOUS replacement or AI-written proof)
        original_content: Original benchmark file content (with PROOF OBVIOUS)
        current_content: Current file content (with proof filled in)
        tlapm_output: Raw tlapm output (for 0-obligation detection)
        tlapm_passed: Whether tlapm exited 0
        parse_theorems_fn: Function to parse theorems from lines (from generate_benchmarks)
    """
    issues = []

    # 1. PROOF OMITTED / bare OMITTED
    issues.extend(detect_proof_omitted(proof_text))

    # 2. Extra AXIOM/ASSUME
    issues.extend(detect_extra_axioms(original_content, current_content))

    # 3. Statement modification
    if parse_theorems_fn:
        issues.extend(detect_statement_modification(original_content, current_content, parse_theorems_fn))

    # 4. Empty PROOF blocks (static check on proof text)
    clean_proof = strip_comments(proof_text)
    issues.extend(detect_empty_proof(clean_proof))

    # 5. Zero total obligations (tlapm ran but proved nothing)
    if tlapm_passed and tlapm_output:
        issues.extend(detect_zero_total_obligations(tlapm_output))

    # 6. Dependency file modification
    if dep_files:
        issues.extend(detect_dependency_modification(dep_files))

    return issues
