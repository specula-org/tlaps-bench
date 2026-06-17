#!/usr/bin/env python3
"""
Generate TLAPS benchmarks from TLA+ proof files.

For each THEOREM/LEMMA/COROLLARY/PROPOSITION with a proof in the source files,
generate a standalone .tla file where:
- All preceding theorems are admitted (PROOF OMITTED)
- The target theorem has its proof stripped (so TLAPS will fail, requiring proof)
- Files with local EXTENDS dependencies are merged into the benchmark file
- Files with INSTANCE dependencies have dependency files copied alongside
- Each benchmark file works standalone (with its dependency files)
"""

import glob
import os
import re

# Modules that tlapm resolves via an -I path, so they should NOT be merged/copied
# as local dependency modules. Two groups:
#   STDLIB_MODULES    — bundled with tlapm 1.6 (~/.tlapm/lib/tlapm/stdlib)
#   COMMUNITY_MODULES — vendored CommunityModules in lib/community/ (added to the
#                       tlapm -I path by install_deps.sh + validate.py/check_proof.py)
# RESOLVABLE_MODULES (the union) is the single source of truth used by this
# generator AND imported by validate.py and scripts/import_tlaps_example.py.
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
    # tlapm 1.6 also bundles these theorem libraries (e.g. Majority's proof needs
    # FiniteSetTheorems' FS_*).
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

# Vendored CommunityModules (lib/community/).
COMMUNITY_MODULES = {
    "SequencesExt",
    "SequencesExtTheorems",
    "FiniteSetsExt",
    "FunctionsExt",
    "BagsExt",
    "Relation",
    "Graphs",
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

# Everything tlapm resolves without copying.
RESOLVABLE_MODULES = STDLIB_MODULES | COMMUNITY_MODULES

# Directories to process (top-level module dirs).
# File lives at <repo>/src/dataset/level1/generate.py; ascend three levels for the repo root.
PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
SOURCE_ROOT = os.path.join(PROJECT_ROOT, "source")
BENCHMARK_DIR = os.path.join(PROJECT_ROOT, "benchmark", "level1")


def find_source_dirs():
    """Find all top-level module directories under source/ containing .tla files."""
    dirs = set()
    for f in glob.glob(os.path.join(SOURCE_ROOT, "**", "*.tla"), recursive=True):
        if ".tlaps" in f:
            continue
        rel = os.path.relpath(f, SOURCE_ROOT)
        parts = rel.split(os.sep)
        if len(parts) >= 2:
            dirs.add(parts[0])
    return sorted(dirs)


def find_tla_files(module_dir):
    """Find all .tla files in a module directory (excluding .tlaps subdirs)."""
    files = []
    for f in glob.glob(os.path.join(module_dir, "**", "*.tla"), recursive=True):
        if ".tlaps" in f:
            continue
        files.append(f)
    return files


def parse_module_name(content):
    """Extract the MODULE name from TLA+ content."""
    m = re.search(r"-+\s*MODULE\s+(\w+)\s*-+", content)
    return m.group(1) if m else None


def parse_extends(content):
    """Extract EXTENDS modules from TLA+ content.

    Handles `\\*` line comments (e.g. tlaplus_examples_glowingRaccoon's
    `EXTENDS Naturals \\* an import`) and multi-line EXTENDS that wraps onto
    indented continuation lines (e.g. tlaplus_examples_allocator's
    SchedulingAllocator_proof).
    """
    lines = content.split("\n")
    for i, line in enumerate(lines):
        m = re.match(r"^EXTENDS\s+(.+)$", line)
        if not m:
            continue
        parts = []
        cur = m.group(1)
        j = i
        while True:
            code = re.split(r"\\\*", cur)[0]  # drop trailing line comment
            parts.append(code)
            if code.rstrip().endswith(","):
                j += 1
                if j < len(lines):
                    cur = lines[j]
                    continue
            break
        joined = " ".join(parts)
        return [x.strip() for x in joined.split(",") if x.strip()]
    return []


def parse_instances(content):
    """Extract INSTANCE references (local module references, not stdlib)."""
    instances = []
    for m in re.finditer(r"(?:(\w+)\s*==\s*)?INSTANCE\s+(\w+)", content):
        alias = m.group(1)
        mod = m.group(2)
        if mod not in RESOLVABLE_MODULES:
            instances.append((alias, mod))
    return instances


def get_local_dependencies(content, available_modules):
    """Get set of local module names this content depends on."""
    deps = set()
    for ext in parse_extends(content):
        if ext in available_modules and ext not in RESOLVABLE_MODULES:
            deps.add(ext)
    for _, mod in parse_instances(content):
        if mod in available_modules:
            deps.add(mod)
    return deps


def get_extends_dependencies(content, available_modules):
    """Get set of local module names this content EXTENDS (safe to merge)."""
    deps = set()
    for ext in parse_extends(content):
        if ext in available_modules and ext not in RESOLVABLE_MODULES:
            deps.add(ext)
    return deps


def get_instance_dependencies(content, available_modules):
    """Get set of local module names this content INSTANCEs (need to copy, not merge)."""
    deps = set()
    for _, mod in parse_instances(content):
        if mod in available_modules:
            deps.add(mod)
    return deps


def get_all_instance_deps(mod, files_by_module, visited=None):
    """Get all transitive INSTANCE + EXTENDS dependencies that need to be copied as files."""
    if visited is None:
        visited = set()
    filepath = files_by_module.get(mod)
    if not filepath:
        return visited
    with open(filepath) as f:
        content = f.read()
    available = set(files_by_module.keys())
    # All dependencies of INSTANCE'd modules (both EXTENDS and INSTANCE) need to be copied
    for _, inst_mod in parse_instances(content):
        if inst_mod in available and inst_mod not in visited:
            visited.add(inst_mod)
            # Recursively get all deps of this module
            get_all_file_deps(inst_mod, files_by_module, visited)
    return visited


def get_all_file_deps(mod, files_by_module, visited=None):
    """Get ALL transitive dependencies of a module (both EXTENDS and INSTANCE)."""
    if visited is None:
        visited = set()
    filepath = files_by_module.get(mod)
    if not filepath:
        return visited
    with open(filepath) as f:
        content = f.read()
    available = set(files_by_module.keys())
    for dep in get_local_dependencies(content, available):
        if dep not in visited:
            visited.add(dep)
            get_all_file_deps(dep, files_by_module, visited)
    return visited


def build_dependency_graph(files_by_module):
    """Build a dependency graph: module -> set of local modules it depends on."""
    available = set(files_by_module.keys())
    graph = {}
    for mod, filepath in files_by_module.items():
        with open(filepath) as f:
            content = f.read()
        graph[mod] = get_local_dependencies(content, available)
    return graph


def topo_sort(graph):
    """Topological sort of modules."""
    visited = set()
    order = []
    temp = set()

    def visit(node):
        if node in temp:
            return  # cycle, skip
        if node in visited:
            return
        temp.add(node)
        for dep in graph.get(node, set()):
            visit(dep)
        temp.discard(node)
        visited.add(node)
        order.append(node)

    for node in graph:
        visit(node)
    return order


def find_all_deps(mod, graph, visited=None):
    """Find all transitive dependencies of a module."""
    if visited is None:
        visited = set()
    for dep in graph.get(mod, set()):
        if dep not in visited:
            visited.add(dep)
            find_all_deps(dep, graph, visited)
    return visited


class TheoremInfo:
    """Represents a theorem/lemma found in the source."""

    def __init__(self, keyword, name, statement_start, statement_end, proof_start, proof_end, has_proof):
        self.keyword = keyword  # THEOREM, LEMMA, etc.
        self.name = name
        self.statement_start = statement_start  # line index of the keyword line
        self.statement_end = statement_end  # line index of last line of statement (before PROOF/BY/OBVIOUS/OMITTED)
        self.proof_start = proof_start  # line index of first proof line (None if no proof)
        self.proof_end = proof_end  # line index of last proof line
        self.has_proof = has_proof  # True if has a non-trivial proof


def find_proof_end(lines, start_idx):
    """Find the end of a proof starting from start_idx.

    A proof ends when we encounter another top-level definition/theorem/separator
    or end of module. We must be careful not to stop on ASSUME/SUFFICES etc. that
    appear inside proof steps.
    """
    i = start_idx

    while i < len(lines):
        line = lines[i].strip()

        # End of module
        if re.match(r"^={3,}", line):
            return i - 1

        if i > start_idx:
            # A new top-level theorem/lemma (these only appear at column 0)
            if re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s", line):
                return i - 1
            # Separator line
            if re.match(r"^-{3,}", line):
                return i - 1
            # New top-level operator definition: must start at column 0 with a name
            # and == but NOT be a proof step. Also exclude lines that are indented
            # or inside proof context.
            orig_line = lines[i]
            if orig_line and not orig_line[0].isspace():
                # At column 0, not indented
                if re.match(r"^\w+(\(.*?\))?\s*==(\s|$)", line) and not re.match(r"^<\d+>", line):
                    return i - 1
                # Top-level CONSTANT/VARIABLE/AXIOM/ASSUME declarations (at column 0 only)
                if re.match(r"^(CONSTANT|CONSTANTS|VARIABLE|VARIABLES|AXIOM|ASSUME|ASSUMPTION)\s", line):
                    return i - 1

        i += 1

    return i - 1


def parse_theorems(lines):
    """Parse all theorems/lemmas from TLA+ file lines.

    Returns list of TheoremInfo objects.
    """
    theorems = []
    i = 0
    comment_depth = 0

    while i < len(lines):
        line = lines[i].strip()

        # Skip lines inside block comments
        if comment_depth > 0:
            for j in range(len(lines[i]) - 1):
                if lines[i][j : j + 2] == "(*":
                    comment_depth += 1
                elif lines[i][j : j + 2] == "*)":
                    comment_depth -= 1
            i += 1
            continue

        # Track comment opens on this line
        line_depth = 0
        for j in range(len(lines[i]) - 1):
            if lines[i][j : j + 2] == "(*":
                line_depth += 1
            elif lines[i][j : j + 2] == "*)":
                line_depth -= 1
        if line_depth > 0:
            comment_depth = line_depth
            i += 1
            continue

        # Match theorem/lemma declaration with a name
        m = re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(\w+)\s*==", line)
        if not m:
            # Also match unnamed theorems like "THEOREM Spec => []Inv"
            m2 = re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(.+)", line)
            if m2 and "==" not in line:
                m = m2  # treat as unnamed theorem, fall through
            if not m:
                i += 1
                continue

        keyword = m.group(1)
        name = f"__unnamed_{i}" if "==" not in line else m.group(2)
        stmt_start = i

        # Scan forward to find where the proof starts (or where the theorem ends)
        # The theorem statement can span multiple lines (ASSUME ... PROVE ...)
        # Proof indicators: PROOF, <N>, BY (at start of line or after statement), OBVIOUS, OMITTED
        proof_start = None
        has_proof = False

        # Check the first line itself for single-line proofs
        # e.g. "THEOREM X == ... BY DEFS ..." or "THEOREM X == ... OBVIOUS"
        # But be careful: "BY" inside the statement body is different
        # For single-line: the theorem declaration + proof are all on one line
        first_line = lines[i]
        # Check for trailing BY/OBVIOUS/OMITTED on the declaration line
        # Only if the entire theorem is on one line (has == and then proof keyword)
        if re.search(r"\bBY\s", first_line) or re.search(r"\bPROOF\s+BY\s", first_line):
            proof_start = i
            has_proof = True
        elif (
            re.search(r"\bOBVIOUS\s*$", first_line)
            or re.search(r"\bOMITTED\s*$", first_line)
            or re.search(r"\bPROOF\s+OMITTED\s*$", first_line)
        ):
            proof_start = i
            has_proof = False

        if proof_start is None:
            j = i + 1
            inner_comment_depth = 0
            while j < len(lines):
                sline = lines[j].strip()
                orig = lines[j]

                # Track comment depth
                line_cd = 0
                for ci in range(len(orig) - 1):
                    if orig[ci : ci + 2] == "(*":
                        line_cd += 1
                    elif orig[ci : ci + 2] == "*)":
                        line_cd -= 1
                inner_comment_depth += line_cd
                if inner_comment_depth > 0:
                    j += 1
                    continue

                # End of module
                if re.match(r"^={3,}", sline):
                    break

                # Another top-level theorem/lemma (not indented)
                if re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s", sline) and (not orig or not orig[0].isspace()):
                    break

                # Separator
                if re.match(r"^-{3,}", sline):
                    break

                # Top-level definitions (not indented, at column 0)
                if orig and not orig[0].isspace():
                    if re.match(r"^[A-Z]\w*(\(.*?\))?\s*==(\s|$)", sline) and not re.match(r"^<\d+>", sline):
                        break
                    # Definitions starting with digits (e.g., 1bOr2bMsgs ==)
                    if re.match(r"^\d\w*\s*==(\s|$)", sline) and not re.match(r"^<\d+>", sline):
                        break
                    if re.match(r"^(CONSTANT|CONSTANTS|VARIABLE|VARIABLES)\s", sline):
                        break

                # Proof indicators
                if sline == "PROOF" or re.match(r"^PROOF\s+BY\s", sline):
                    proof_start = j
                    has_proof = True
                    break
                if sline == "OBVIOUS" or sline.startswith("OBVIOUS "):
                    proof_start = j
                    has_proof = False
                    break
                if sline == "OMITTED" or sline == "PROOF OMITTED" or sline.startswith("PROOF OMITTED "):
                    proof_start = j
                    has_proof = False
                    break
                if re.match(r"^<\d+>", sline):
                    proof_start = j
                    has_proof = True
                    break
                # BY at start of line (possibly indented)
                if re.match(r"^\s*BY\s", orig) or sline.startswith("BY ") or sline == "BY":
                    proof_start = j
                    has_proof = True
                    break

                j += 1

        if proof_start is not None:
            stmt_end = (proof_start - 1) if proof_start > stmt_start else stmt_start
            proof_end = find_proof_end(lines, proof_start)
        else:
            # No proof body in source — the forward scan stopped at `j` (the next
            # top-level declaration or end of module). A theorem's multi-line
            # statement is its keyword line plus any *indented* continuation
            # lines (TLA+ uses indentation to denote line continuation). Blank
            # lines and comment blocks (col-0) between this theorem and the
            # next decl belong to the next decl, not to this one.
            stmt_end = stmt_start
            for k in range(stmt_start + 1, j):
                line = lines[k]
                if not line.strip():
                    continue  # blank line — not part of statement
                if not line[0].isspace():
                    break  # col-0 line (comment block or other) — not a continuation
                stmt_end = k
            proof_end = stmt_end

        # Include all theorems (even OMITTED/OBVIOUS) so generate_benchmark_file
        # can properly handle their line ranges (e.g., skip commented proof sketches)
        theorems.append(TheoremInfo(keyword, name, stmt_start, stmt_end, proof_start, proof_end, has_proof))

        i = (proof_end + 1) if proof_end is not None else (j if proof_start is None else proof_end + 1)
        continue

    return theorems


def extract_preamble(lines, theorems):
    """Extract everything before the first theorem - the preamble (module header, extends, constants, vars, defs)."""
    if not theorems:
        return lines[:]
    return lines[: theorems[0].statement_start]


def get_theorem_statement_lines(lines, thm):
    """Get the statement lines of a theorem (without proof)."""
    # Handle single-line theorem with proof on same line
    if thm.proof_start == thm.statement_start:
        line = lines[thm.statement_start]
        # Remove the BY/OBVIOUS/OMITTED part
        # Find the theorem body by removing proof
        for pat in [r"\s+BY\s+.*$", r"\s+OBVIOUS\s*$", r"\s+OMITTED\s*$", r"\s+PROOF\s+OMITTED\s*$"]:
            line = re.sub(pat, "", line)
        return [line]

    result = lines[thm.statement_start : thm.statement_end + 1]
    # Clean trailing empty lines
    while result and result[-1].strip() == "":
        result.pop()
    # Remove trailing comment blocks that contain proof steps (e.g. <1>2.)
    # Properly handle nested/inline comments like (* PTL *)
    while result:
        last = len(result) - 1
        if result[last].strip().endswith("*)"):
            # Scan backward tracking comment depth to find the matching opener
            depth = 0
            comment_start = None
            for j in range(last, -1, -1):
                line_text = result[j]
                # Count opens/closes on this line (scan left to right)
                opens = 0
                closes = 0
                for k in range(len(line_text) - 1):
                    if line_text[k : k + 2] == "(*":
                        opens += 1
                    elif line_text[k : k + 2] == "*)":
                        closes += 1
                depth += closes - opens  # going backward: closes add depth, opens reduce
                if depth <= 0 and opens > 0:
                    comment_start = j
                    break
            if comment_start is not None and comment_start > 0:
                comment_text = "\n".join(result[comment_start : last + 1])
                if re.search(r"<\d+>", comment_text):
                    result = result[:comment_start]
                    while result and result[-1].strip() == "":
                        result.pop()
                    continue
        break
    return result


def get_theorem_proof_lines(lines, thm):
    """Dual of get_theorem_statement_lines: return a theorem's proof body lines.

    For an inline proof (proof on the same line as the declaration, e.g.
    'LEMMA Foo == x  BY DEF y'), return only the proof tail (['BY DEF y'])
    rather than the whole declaration line -- otherwise porting the proof into
    a benchmark re-declares the theorem and produces a malformed module. For a
    multi-line proof, return lines[proof_start:proof_end+1] verbatim.
    """
    if thm.proof_start is None or not thm.has_proof:
        return []
    if thm.proof_start == thm.statement_start:
        line = lines[thm.statement_start]
        m = re.search(r"\s+(PROOF\s+BY\b.*|BY\b.*)$", line)
        return [m.group(1)] if m else [line]
    return lines[thm.proof_start : thm.proof_end + 1]


def merge_files(files_by_module, dep_graph, target_module):
    """Merge all dependencies of target_module into a single content string.

    Returns merged lines and the module name to use.
    """
    all_deps = find_all_deps(target_module, dep_graph)

    if not all_deps:
        # No local dependencies, just return the file content
        with open(files_by_module[target_module]) as f:
            return f.readlines(), target_module

    # Topological order of all deps + target
    order = topo_sort(dep_graph)
    relevant = [m for m in order if m in all_deps or m == target_module]

    # Merge: collect all extends (stdlib only), then all content from each module
    all_extends = set()
    merged_body_lines = []

    for mod in relevant:
        with open(files_by_module[mod]) as f:
            content = f.read()

        mod_lines = content.split("\n")

        # Collect resolvable extends
        for ext in parse_extends(content):
            if ext in RESOLVABLE_MODULES:
                all_extends.add(ext)

        # Extract body (between MODULE header and ending ====)
        body_start = None
        body_end = None
        for idx, line in enumerate(mod_lines):
            if body_start is None and re.match(r"^-+\s*MODULE\s+\w+\s*-+", line.strip()):
                body_start = idx + 1
            if re.match(r"^={3,}", line.strip()):
                body_end = idx

        if body_start is None:
            continue
        if body_end is None:
            body_end = len(mod_lines)

        body = mod_lines[body_start:body_end]

        # Remove EXTENDS line(s) from body (we'll put a unified one). Skip the
        # EXTENDS line and any continuation lines of a multi-line EXTENDS, whose
        # wrapped 2nd line would otherwise be orphaned and cause a parse error
        # (e.g. tlaplus_examples_allocator's SchedulingAllocator_proof).
        filtered_body = []
        in_extends = False
        for line in body:
            if in_extends:
                # still consuming continuation lines of a multi-line EXTENDS;
                # stop after a line whose code part lacks a trailing comma
                code = re.split(r"\\\*", line)[0].rstrip()
                in_extends = code.endswith(",")
                continue
            if re.match(r"^EXTENDS\s", line.strip()):
                code = re.split(r"\\\*", line)[0].rstrip()
                in_extends = code.endswith(",")  # multi-line if trailing comma
                continue
            filtered_body.append(line)

        if mod != target_module:
            merged_body_lines.append(f"(* ---- Content from module {mod} ---- *)")
        merged_body_lines.extend(filtered_body)
        if mod != target_module:
            merged_body_lines.append("")

    # Build final content
    header_lines = []
    extends_str = ", ".join(sorted(all_extends)) if all_extends else ""

    # We'll use a placeholder module name; caller will set it
    header_lines.append("---- MODULE __PLACEHOLDER__ ----")
    if extends_str:
        header_lines.append(f"EXTENDS {extends_str}")

    result_lines = header_lines + merged_body_lines + ["=" * 40]
    return [ln + "\n" for ln in result_lines], target_module


def strip_all_proofs(lines, theorems):
    """Strip all proofs from a file, replacing them with PROOF OMITTED.

    Used for dependency files that are copied alongside benchmarks.
    """
    result = []
    i = 0
    while i < len(lines):
        found_thm = None
        for idx, thm in enumerate(theorems):
            if i == thm.statement_start:
                found_thm = idx
                break

        if found_thm is not None:
            thm = theorems[found_thm]
            end = thm.proof_end if thm.proof_end is not None else thm.statement_end
            if not thm.has_proof and thm.proof_start is not None:
                # Source already has explicit OMITTED/OBVIOUS — copy verbatim
                for li in range(thm.statement_start, end + 1):
                    result.append(lines[li])
            else:
                # Either has a real proof (which we strip) OR has no proof at all
                # (in which case we still need to mark it OMITTED so the file parses
                # as a valid TLAPS module — bare THEOREM without proof obligates
                # checker to either accept or reject it).
                stmt_lines = get_theorem_statement_lines(lines, thm)
                result.extend(stmt_lines)
                result.append("  PROOF OMITTED")
                result.append("")
            i = end + 1
            continue

        # Check if inside a theorem range
        inside = False
        for thm in theorems:
            start = thm.statement_start
            end = thm.proof_end if thm.proof_end is not None else thm.statement_end
            if start < i <= end:
                inside = True
                break
        if inside:
            i += 1
            continue

        result.append(lines[i])
        i += 1

    return "\n".join(result)


def generate_benchmark_file(lines_or_content, theorems, target_idx, module_name, benchmark_name):
    """Generate a benchmark file for the target_idx-th theorem.

    - All theorems before target_idx: keep statement, add PROOF OMITTED
    - Target theorem: keep statement, remove proof entirely
    - All theorems after target_idx: removed entirely
    """
    if isinstance(lines_or_content, str):
        lines = lines_or_content.split("\n")
    else:
        lines = [ln.rstrip("\n") for ln in lines_or_content]

    # We'll rebuild the file by going through lines and replacing theorem sections
    result = []

    # Track which line ranges belong to which theorems
    thm_ranges = {}
    for idx, thm in enumerate(theorems):
        start = thm.statement_start
        end = thm.proof_end if thm.proof_end is not None else thm.statement_end
        thm_ranges[idx] = (start, end)

    i = 0
    while i < len(lines):
        # Check if this line is the start of any theorem
        found_thm = None
        for idx, thm in enumerate(theorems):
            if i == thm.statement_start:
                found_thm = idx
                break

        if found_thm is not None:
            thm = theorems[found_thm]
            stmt_lines = get_theorem_statement_lines(lines, thm)

            if found_thm < target_idx:
                # Preceding theorem: admit it
                if not thm.has_proof:
                    # Already OMITTED/OBVIOUS — copy original lines verbatim
                    end = thm.proof_end if thm.proof_end is not None else thm.statement_end
                    for li in range(thm.statement_start, end + 1):
                        result.append(lines[li])
                else:
                    result.extend(stmt_lines)
                    result.append("  PROOF OMITTED")
                    result.append("")
            elif found_thm == target_idx:
                # Target theorem: replace proof with OBVIOUS (will fail for non-trivial theorems)
                result.extend(stmt_lines)
                result.append("PROOF OBVIOUS")
                result.append("")
            else:
                # Theorems after target: skip entirely
                pass

            # Skip past the theorem's proof
            end = thm.proof_end if thm.proof_end is not None else thm.statement_end
            i = end + 1
            continue

        # Check if this line is inside a theorem range (shouldn't happen, but safety)
        inside = False
        for _idx, (start, end) in thm_ranges.items():
            if start < i <= end:
                inside = True
                break

        if inside:
            i += 1
            continue

        # For lines after the target theorem, skip non-theorem content too
        # (definitions that may depend on later theorems)
        # Actually, keep all definitions/content that appears before or between theorems
        # up to the target. After the target, only keep the module end.
        if found_thm is None:
            # Check if we're past the target theorem
            if target_idx < len(theorems) and i > theorems[target_idx].statement_start:
                # Only keep the module end line (====)
                if re.match(r"^={3,}", lines[i].strip()):
                    result.append(lines[i])
                i += 1
                continue
            result.append(lines[i])

        i += 1

    # Ensure module ends with ====
    if not any(re.match(r"^={3,}", ln.strip()) for ln in result[-3:] if ln.strip()):
        result.append("=" * 40)

    # Remove comment blocks containing proof steps (e.g. <1>2.)
    # Must properly track nested comment depth
    cleaned = []
    comment_depth = 0
    comment_buf = []
    for line in result:
        # Count comment opens/closes on this line
        line_opens = 0
        line_closes = 0
        for k in range(len(line) - 1):
            if line[k : k + 2] == "(*":
                line_opens += 1
            elif line[k : k + 2] == "*)":
                line_closes += 1

        if comment_depth == 0 and line_opens > 0:
            # Entering a comment block
            comment_depth = line_opens - line_closes
            if comment_depth > 0:
                comment_buf = [line]
            elif comment_depth == 0:
                # Single-line comment (opens and closes on same line)
                if not re.search(r"<\d+>\d+\.", line):
                    cleaned.append(line)
            # comment_depth < 0 shouldn't happen
        elif comment_depth > 0:
            comment_buf.append(line)
            comment_depth += line_opens - line_closes
            if comment_depth <= 0:
                # Comment block closed
                comment_text = "\n".join(comment_buf)
                if not re.search(r"<\d+>\d+\.", comment_text):
                    cleaned.extend(comment_buf)
                comment_buf = []
                comment_depth = 0
        else:
            cleaned.append(line)
    if comment_buf:
        cleaned.extend(comment_buf)
    result = cleaned

    # Fix unclosed comments: count (* and *) and close any open ones
    depth = 0
    for line in result:
        for j in range(len(line) - 1):
            if line[j : j + 2] == "(*":
                depth += 1
            elif line[j : j + 2] == "*)":
                depth -= 1
    # Insert closing comments before the ==== line
    if depth > 0:
        eq_idx = next(
            (i for i in range(len(result) - 1, -1, -1) if re.match(r"^={3,}", result[i].strip())), len(result)
        )
        for _ in range(depth):
            result.insert(eq_idx, "*)")

    # Replace module name in header
    final = []
    for line in result:
        if re.match(r"^-+\s*MODULE\s+\w+\s*-+", line.strip()):
            line = re.sub(r"MODULE\s+\w+", f"MODULE {benchmark_name}", line)
        if "__PLACEHOLDER__" in line:
            line = line.replace("__PLACEHOLDER__", benchmark_name)
        final.append(line)

    return "\n".join(final)


def process_module_dir(module_dir_name):
    """Process a single module directory and generate benchmarks."""
    module_path = os.path.join(SOURCE_ROOT, module_dir_name)
    tla_files = find_tla_files(module_path)

    if not tla_files:
        return 0

    # Build module -> filepath mapping
    files_by_module = {}
    for f in tla_files:
        with open(f) as fh:
            content = fh.read()
        mod_name = parse_module_name(content)
        if mod_name:
            files_by_module[mod_name] = f

    # Build dependency graph
    build_dependency_graph(files_by_module)
    available = set(files_by_module.keys())

    benchmark_count = 0
    out_dir = os.path.join(BENCHMARK_DIR, module_dir_name)

    for mod_name, filepath in files_by_module.items():
        with open(filepath) as f:
            content = f.read()

        raw_lines = content.split("\n")
        theorems = parse_theorems(raw_lines)

        if not theorems or not any(t.has_proof for t in theorems):
            continue
        # - EXTENDS local deps: merge into the benchmark file
        # - INSTANCE local deps: copy as separate files alongside benchmark
        extends_deps = get_extends_dependencies(content, available)
        instance_deps = get_instance_dependencies(content, available)

        # For EXTENDS deps, also get their transitive EXTENDS deps (for merging)
        all_extends_deps = set()
        for ed in extends_deps:
            all_extends_deps.add(ed)
            # Get transitive EXTENDS-only deps
            ed_filepath = files_by_module.get(ed)
            if ed_filepath:
                with open(ed_filepath) as f:
                    ed_content = f.read()
                all_extends_deps |= get_extends_dependencies(ed_content, available)

        # For INSTANCE deps, collect all files that need to be copied
        # (the INSTANCE'd module + all its transitive deps)
        # Include INSTANCE deps from both the main module AND merged EXTENDS deps
        files_to_copy = set()
        for inst_mod in instance_deps:
            files_to_copy.add(inst_mod)
            get_all_file_deps(inst_mod, files_by_module, files_to_copy)
        # Also get INSTANCE deps from EXTENDS deps (they're merged into the benchmark)
        for ed in all_extends_deps:
            ed_filepath = files_by_module.get(ed)
            if ed_filepath:
                with open(ed_filepath) as f:
                    ed_content = f.read()
                for _, inst_mod in parse_instances(ed_content):
                    if inst_mod in available and inst_mod not in all_extends_deps:
                        files_to_copy.add(inst_mod)
                        get_all_file_deps(inst_mod, files_by_module, files_to_copy)
        # Remove any extends deps from files_to_copy (they'll be merged)
        files_to_copy -= all_extends_deps

        # A copied dep file keeps its own EXTENDS/INSTANCE clauses, so close
        # files_to_copy under transitive deps — otherwise a merged-only module
        # that a copied dep file references is absent (e.g. tlaplus_examples_
        # MisraReachability copies Reachable but it EXTENDS Reachability).
        copy_closure = set(files_to_copy)
        for cf in list(files_to_copy):
            get_all_file_deps(cf, files_by_module, copy_closure)
        files_to_copy = copy_closure

        # Merge only EXTENDS dependencies
        if all_extends_deps:
            # Build a restricted dep graph for EXTENDS-only merging
            extends_graph = {}
            for ed in all_extends_deps:
                ed_filepath = files_by_module.get(ed)
                if ed_filepath:
                    with open(ed_filepath) as f:
                        ed_content = f.read()
                    extends_graph[ed] = get_extends_dependencies(ed_content, available) & all_extends_deps
            extends_graph[mod_name] = all_extends_deps

            merged_lines, _ = merge_files(files_by_module, extends_graph, mod_name)
            work_lines = [ln.rstrip("\n") for ln in merged_lines]
            theorems = parse_theorems(work_lines)
            if not theorems or not any(t.has_proof for t in theorems):
                continue
        else:
            work_lines = raw_lines

        # Generate one benchmark file per theorem
        source_basename = os.path.splitext(os.path.basename(filepath))[0]

        # Track used names to handle duplicates
        name_counts = {}
        for idx, thm in enumerate(theorems):
            # Skip unnamed theorems as benchmark targets (they still get PROOF OMITTED as preceding theorems)
            if thm.name.startswith("__unnamed_"):
                continue
            # Skip theorems without real proofs (PROOF OMITTED / OBVIOUS only)
            if not thm.has_proof:
                continue
            base_name = f"{source_basename}_{thm.name}"
            if base_name in name_counts:
                name_counts[base_name] += 1
                benchmark_name = f"{base_name}_{name_counts[base_name]}"
            else:
                name_counts[base_name] = 0
                benchmark_name = base_name
            benchmark_file = os.path.join(out_dir, f"{benchmark_name}.tla")

            os.makedirs(out_dir, exist_ok=True)

            content = generate_benchmark_file(work_lines, theorems, idx, mod_name, benchmark_name)

            with open(benchmark_file, "w") as f:
                f.write(content)

            # Copy INSTANCE dependency files alongside the benchmark
            # Strip all proofs from copied files (replace with PROOF OMITTED)
            # to avoid leaking proof information
            for dep_mod in files_to_copy:
                dep_filepath = files_by_module.get(dep_mod)
                if dep_filepath:
                    dest = os.path.join(out_dir, os.path.basename(dep_filepath))
                    if not os.path.exists(dest):
                        # Read, strip proofs, write
                        with open(dep_filepath) as df:
                            dep_content = df.read()
                        dep_lines = dep_content.split("\n")
                        dep_theorems = parse_theorems(dep_lines)
                        if dep_theorems:
                            # Use generate_benchmark_file logic but admit ALL theorems
                            stripped = strip_all_proofs(dep_lines, dep_theorems)
                            with open(dest, "w") as df:
                                df.write(stripped)
                        else:
                            # No theorems, just copy as-is
                            import shutil

                            shutil.copy2(dep_filepath, dest)

            benchmark_count += 1
            print(f"  Generated: {os.path.relpath(benchmark_file, SOURCE_ROOT)}")

    return benchmark_count


# ---------------------------------------------------------------------------
# Shared-model L1 (opt-in via --shared-model). Reuses the certified L2 dump
# engine (src/dataset/level2/generate.py) for the model extraction + helpers,
# and adds an L1-specific task builder. Default (no flag) keeps the regex path.
# ---------------------------------------------------------------------------
def _load_l2_engine():
    """Load the L2 generator as the shared-model engine. L2 does
    `from generate import ...` expecting THIS module's helpers, so alias us as
    `generate` first."""
    import importlib.util
    import sys

    sys.modules.setdefault("generate", sys.modules.get("__main__", sys.modules[__name__]))
    path = os.path.join(os.path.dirname(__file__), "..", "level2", "generate.py")
    spec = importlib.util.spec_from_file_location("l2_sm_engine", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["l2_sm_engine"] = mod
    spec.loader.exec_module(mod)
    return mod


def _is_structured_proof(sm, t, lines):
    """True iff the proof is a real structured/BY proof (not OBVIOUS/OMITTED).
    Strips comments first so `OBVIOUS (*{hint}*)` is seen as OBVIOUS."""
    ploc = t.get("proof_loc")
    if not (ploc and ploc.get("line_start", -1) > 0):
        return False
    body = "".join(lines[ploc["line_start"] - 1 : ploc["line_end"]])
    body = sm.strip_comments(body).strip()
    if body.startswith("PROOF"):
        body = body[5:].lstrip()
    return body not in ("OMITTED", "OBVIOUS", "")


def _proof_edit(source_lines, ploc, keyword):
    """An apply_edits tuple that replaces a proof body with `keyword`, PRESERVING
    any statement text that shares the proof's first line. One-line lemmas like
    `LEMMA X == s  BY DEF Y` put the proof (col 41) on the statement line (cols
    1-40); a whole-line replace would delete the statement and leave a stray
    `PROOF OMITTED`."""
    line = source_lines[ploc["line_start"] - 1]
    col = ploc.get("column_start", 1)
    prefix = line[: col - 1].rstrip()
    repl = (prefix + "\n  " + keyword + "\n") if prefix else (keyword + "\n")
    return (ploc["line_start"], ploc["line_end"], repl)


def build_l1_task(sm, source_lines, dump, target_thm, bench_module_name, model_set, module):
    """L1 task: keep ALL scaffolding (Inv etc.), admit STRUCTURED preceding
    proofs as PROOF OMITTED (keep OBVIOUS verbatim → it still emits an
    obligation), stub the target PROOF OBVIOUS, drop later theorems, keep
    comments. If model_set is non-empty, EXTEND the shared model (delete its ops
    + the inherited decls); else stay self-contained."""
    use_model = bool(model_set)
    edits = list(sm._decl_edits(dump)) if use_model else []
    tid = id(target_thm)
    tstart = target_thm["loc"]["line_start"]
    for t in dump["theorems"]:
        loc, ploc = t["loc"], t.get("proof_loc")
        has_body = ploc and ploc.get("line_start", -1) > 0
        if id(t) == tid:
            if has_body:
                edits.append(_proof_edit(source_lines, ploc, "PROOF OBVIOUS"))
        elif loc["line_start"] < tstart:
            if has_body and _is_structured_proof(sm, t, source_lines):
                edits.append(_proof_edit(source_lines, ploc, "PROOF OMITTED"))
        else:
            edits.append((loc["line_start"], loc["line_end"], ""))
    if use_model:
        for o in dump["operators"]:
            if o["name"] in model_set:
                edits.append((o["loc"]["line_start"], o["loc"]["line_end"], ""))
        for inst in dump["instances"]:
            if inst.get("name") and inst["name"] in model_set:
                edits.append((inst["loc"]["line_start"], inst["loc"]["line_end"], ""))
    text = sm.apply_edits(source_lines, edits)
    if use_model:
        text = sm._strip_bare_decls(text)
        text = sm._rewrite_extends_line(text, module)
    text = sm._rename_header(text, bench_module_name)
    return sm._sm_tidy(text)


def generate_shared_model_l1(output_root=None):
    """Dump-based L1 generation: one shared `<Module>.tla` per output dir +
    EXTENDS-based L1 tasks. Mirrors the L2 shared-model layout."""
    import shutil
    import sys

    sm = _load_l2_engine()
    output_root = output_root or BENCHMARK_DIR

    if os.path.exists(output_root):
        shutil.rmtree(output_root)
    os.makedirs(output_root, exist_ok=True)

    targets = []
    for f in sorted(glob.glob(os.path.join(SOURCE_ROOT, "**", "*.tla"), recursive=True)):
        if ".tlaps" in f:
            continue
        subdir = os.path.relpath(f, SOURCE_ROOT).split(os.sep)[0]
        targets.append((f, subdir))
    sibling_deps = sm.compute_sibling_deps(targets)

    total = 0
    for path, subdir in targets:
        try:
            dump = sm.dump_sany(path)
        except Exception as e:
            print(f"  SANY failed on {path}: {e}", file=sys.stderr)
            continue
        module = dump["module"]
        with open(path, encoding="utf-8") as fh:
            lines = fh.readlines()
        # L1 targets: NAMED theorems with a structured proof.
        l1_targets = [t for t in dump["theorems"] if t.get("name") and _is_structured_proof(sm, t, lines)]
        if not l1_targets:
            continue
        out_dir = os.path.join(output_root, subdir)
        os.makedirs(out_dir, exist_ok=True)

        model_set = set()
        if module not in sibling_deps.get(subdir, set()):
            model_set, _ = sm.compute_model_set(dump, l1_targets)
            if model_set:
                model_text = sm.build_model(lines, dump, model_set)
                with open(os.path.join(out_dir, f"{module}.tla"), "w") as f:
                    f.write(model_text)

        base = os.path.splitext(os.path.basename(path))[0]
        used = {}
        reachable_all = {i["name"] for i in dump["instances"] if i.get("name")}
        for t in l1_targets:
            name = f"{base}_{t['name']}"
            if name in used:
                used[name] += 1
                bench = f"{name}_{used[name]}"
            else:
                used[name] = 0
                bench = name
            text = build_l1_task(sm, lines, dump, t, bench, model_set, module)
            with open(os.path.join(out_dir, f"{bench}.tla"), "w") as f:
                f.write(text)
            total += 1
            print(f"  generated: {os.path.relpath(os.path.join(out_dir, bench + '.tla'), PROJECT_ROOT)}")
        sm.copy_deps(dump, path, out_dir, reachable_all)
    print(f"\nTotal L1 benchmarks (shared-model): {total}")
    return total


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Generate L1 benchmarks.")
    parser.add_argument(
        "--shared-model",
        action="store_true",
        help="Emit one proof-free <Module>.tla model per output dir "
        "and have tasks EXTEND it instead of inlining the spec.",
    )
    parser.add_argument("--output-dir", default=None, help="Output directory (default: benchmark/level1)")
    args = parser.parse_args()

    if args.shared_model:
        generate_shared_model_l1(output_root=args.output_dir)
        return

    # Clean benchmark dir
    if os.path.exists(BENCHMARK_DIR):
        import shutil

        shutil.rmtree(BENCHMARK_DIR)
    os.makedirs(BENCHMARK_DIR, exist_ok=True)

    module_dirs = find_source_dirs()
    total = 0

    for mod_dir in module_dirs:
        print(f"\nProcessing {mod_dir}/")
        count = process_module_dir(mod_dir)
        total += count
        if count:
            print(f"  -> {count} benchmarks")

    print(f"\nTotal benchmarks generated: {total}")


if __name__ == "__main__":
    main()
