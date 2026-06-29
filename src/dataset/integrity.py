"""Dataset integrity guard: no proof content may leak outside a module.

A benchmark `.tla` file is a sequence of TLA+ modules, each delimited by a
``---- MODULE X ----`` header and a ``====`` terminator. Anything OUTSIDE a
module (after a ``====``, before the next header) is ignored by SANY/tlapm — so
a generator that fails to truncate the original source leaves the full reference
proof dangling there. The tooling never notices (it parses only module bodies),
but an agent that *reads the file* sees the answer. This is exactly the CRDT
contamination bug, which had been fixed once and silently regressed.

This guard makes that class of leak impossible to ship unnoticed: it scans every
benchmark file and FAILS if any `THEOREM`/`LEMMA`/proof step appears while not
inside a module. Wire it into CI / the dataset build so a regression is caught at
the source, regardless of which generator (or rename) reintroduced it.

Benign trailing text — author notes, TLC stats tables, ASCII diagrams, comments —
is NOT flagged: only real proof/theorem tokens on non-comment lines count.

Run:  PYTHONPATH=src python3 -m dataset.integrity [benchmark_root ...]
"""

from __future__ import annotations

import argparse
import glob
import os
import re
import sys

# A line that is only `=` signs (4+) — a TLA+ module terminator.
_MODULE_END = re.compile(r"^={4,}\s*$")
# A module header line: `---- MODULE Name ----`.
_MODULE_HEADER = re.compile(r"^-+\s*MODULE\s+\w+\s*-+\s*$")
# Proof-bearing tokens that must never appear outside a module body. Theorem
# statements (the goal) and proof steps (the answer) both count.
_LEAK_TOKEN = re.compile(
    r"^[ \t]*("
    r"THEOREM|LEMMA|COROLLARY|PROPOSITION|AXIOM"  # statements
    r"|PROOF\b|OBVIOUS\b|QED\b|BY\b|USE\b|HIDE\b|DEFINE\b|SUFFICES\b|WITNESS\b|PICK\b"  # proof steps
    r"|<\d+>"  # structured proof step labels  <1>, <2>3, <1>a
    r")"
)


def iter_leaks(text: str):
    """Yield (lineno, line) for each proof/theorem token found OUTSIDE a module.

    A simple state machine tracks module nesting and `(* *)` / `\\*` comments,
    so author prose and trailing TLC tables never trigger it. ``module_depth`` is
    a counter, not a flag: TLA+ allows a nested ``---- MODULE Inner ---- … ====``
    inside an outer module, and the outer module continues after the inner's
    terminator — a flag would wrongly treat the outer body as "outside a module".
    """
    module_depth = 0  # 0 = outside every module; each header deepens, each ==== rises
    block_comment = 0  # depth of (* ... *)
    for i, raw in enumerate(text.splitlines(), start=1):
        line = raw
        # Strip block comments (handles single-line `(* ... *)`; tracks depth for
        # multi-line). Crude but sufficient: we only need to avoid matching tokens
        # that live inside comments.
        if block_comment:
            end = line.find("*)")
            if end == -1:
                continue
            line = line[end + 2 :]
            block_comment -= 1
        # Remove inline `(* ... *)` spans on this line.
        while "(*" in line:
            start = line.find("(*")
            end = line.find("*)", start + 2)
            if end == -1:
                block_comment += 1
                line = line[:start]
                break
            line = line[:start] + " " + line[end + 2 :]
        # Strip `\* line comment`.
        line = re.sub(r"\\\*.*$", "", line)
        stripped = line.strip()
        if not stripped:
            continue

        if _MODULE_HEADER.match(stripped):
            module_depth += 1
            continue
        if _MODULE_END.match(stripped):
            module_depth = max(0, module_depth - 1)
            continue
        if module_depth == 0 and _LEAK_TOKEN.match(line):
            yield i, raw.rstrip()


def check_file(path: str) -> list[tuple[int, str]]:
    try:
        with open(path, encoding="utf-8", errors="ignore") as f:
            text = f.read()
    except OSError:
        return []
    return list(iter_leaks(text))


def check_dir(root: str) -> dict[str, list[tuple[int, str]]]:
    """Map each contaminated .tla under `root` to its leak findings."""
    out: dict[str, list[tuple[int, str]]] = {}
    for f in sorted(glob.glob(os.path.join(root, "**", "*.tla"), recursive=True)):
        leaks = check_file(f)
        if leaks:
            out[f] = leaks
    return out


def default_roots() -> list[str]:
    repo = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
    return [
        # The upstream specs the generators read — the true origin: a malformed
        # source (proof dangling after ====) propagates into every derived task.
        os.path.join(repo, "source"),
        # The generated benchmark suites the agent actually sees.
        os.path.join(repo, "benchmark", "proof-completion"),
        os.path.join(repo, "benchmark", "proof-from-scratch"),
    ]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("roots", nargs="*", help="benchmark dirs (default: source + both modes)")
    ap.add_argument("--quiet", action="store_true", help="only print the summary line")
    args = ap.parse_args()
    roots = args.roots or default_roots()

    total_files = 0
    bad: dict[str, list[tuple[int, str]]] = {}
    for root in roots:
        if not os.path.isdir(root):
            print(f"skip (not a dir): {root}", file=sys.stderr)
            continue
        total_files += len(glob.glob(os.path.join(root, "**", "*.tla"), recursive=True))
        bad.update(check_dir(root))

    if bad:
        if not args.quiet:
            for f, leaks in bad.items():
                rel = f.split("benchmark/")[-1]
                first = leaks[0]
                print(f"  CONTAMINATED {rel}  ({len(leaks)} leaked tokens; first @ line {first[0]}: {first[1][:60]!r})")
        print(f"\nFAIL: {len(bad)}/{total_files} files have proof/theorem content OUTSIDE a module (answer leak).")
        return 1
    print(f"OK: {total_files} files clean — no proof/theorem leaks outside a module.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
