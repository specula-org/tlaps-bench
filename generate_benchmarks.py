#!/usr/bin/env python3
"""
Generate TLAPS benchmarks from TLA+ proof files.

For each THEOREM/LEMMA/COROLLARY/PROPOSITION with a proof in the source files,
generate a standalone .tla file where:
- All preceding theorems are admitted (PROOF OMITTED)
- The target theorem has its proof stripped (so TLAPS will fail, requiring proof)
- Files with local EXTENDS/INSTANCE dependencies are merged into a single file
- Each benchmark file is standalone
"""

import os
import re
import sys
import glob
from collections import defaultdict
from pathlib import Path
from typing import List, Tuple, Optional, Dict, Set

# Standard TLA+ library modules (should NOT be merged)
STDLIB_MODULES = {
    'TLAPS', 'Integers', 'Naturals', 'Sequences', 'FiniteSets', 'Reals',
    'Bags', 'TLC', 'NaturalsInduction', 'SequenceTheorems',
    'WellFoundedInduction', 'ProtoReals', 'Functions', 'SequenceOpTheorems',
    'BagsTheorems', 'RealNumberTheorems', 'TLAPS',
}

# Directories to process (top-level module dirs)
SOURCE_ROOT = os.path.dirname(os.path.abspath(__file__))
BENCHMARK_DIR = os.path.join(SOURCE_ROOT, 'benchmark')


def find_source_dirs():
    """Find all top-level module directories containing .tla files (exclude .tlaps dirs)."""
    dirs = set()
    for f in glob.glob(os.path.join(SOURCE_ROOT, '**', '*.tla'), recursive=True):
        if '.tlaps' in f or 'benchmark' in f:
            continue
        # Get the top-level dir relative to SOURCE_ROOT
        rel = os.path.relpath(f, SOURCE_ROOT)
        parts = rel.split(os.sep)
        if len(parts) >= 2:
            # Use first component as module group; for nested like Euclid/Euclid-Hyperbook/, use first two
            dirs.add(parts[0])
    return sorted(dirs)


def find_tla_files(module_dir):
    """Find all .tla files in a module directory (excluding .tlaps subdirs)."""
    files = []
    for f in glob.glob(os.path.join(module_dir, '**', '*.tla'), recursive=True):
        if '.tlaps' in f:
            continue
        files.append(f)
    return files


def parse_module_name(content):
    """Extract the MODULE name from TLA+ content."""
    m = re.search(r'-+\s*MODULE\s+(\w+)\s*-+', content)
    return m.group(1) if m else None


def parse_extends(content):
    """Extract EXTENDS modules from TLA+ content."""
    m = re.search(r'^EXTENDS\s+(.+)$', content, re.MULTILINE)
    if not m:
        return []
    return [x.strip() for x in m.group(1).split(',')]


def parse_instances(content):
    """Extract INSTANCE references (local module references, not stdlib)."""
    instances = []
    for m in re.finditer(r'(?:(\w+)\s*==\s*)?INSTANCE\s+(\w+)', content):
        alias = m.group(1)
        mod = m.group(2)
        if mod not in STDLIB_MODULES:
            instances.append((alias, mod))
    return instances


def get_local_dependencies(content, available_modules):
    """Get set of local module names this content depends on."""
    deps = set()
    for ext in parse_extends(content):
        if ext in available_modules and ext not in STDLIB_MODULES:
            deps.add(ext)
    for _, mod in parse_instances(content):
        if mod in available_modules:
            deps.add(mod)
    return deps


def build_dependency_graph(files_by_module):
    """Build a dependency graph: module -> set of local modules it depends on."""
    available = set(files_by_module.keys())
    graph = {}
    for mod, filepath in files_by_module.items():
        with open(filepath, 'r') as f:
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
        self.statement_end = statement_end      # line index of last line of statement (before PROOF/BY/OBVIOUS/OMITTED)
        self.proof_start = proof_start          # line index of first proof line (None if no proof)
        self.proof_end = proof_end              # line index of last proof line
        self.has_proof = has_proof              # True if has a non-trivial proof


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
        if re.match(r'^={3,}', line):
            return i - 1

        if i > start_idx:
            # A new top-level theorem/lemma
            if re.match(r'^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s', line):
                return i - 1
            # Separator line
            if re.match(r'^-{3,}', line):
                return i - 1
            # New top-level operator definition: must start at column 0 with a name
            # and == but NOT be a proof step. Also exclude lines that are indented
            # or inside proof context.
            orig_line = lines[i]
            if orig_line and not orig_line[0].isspace():
                # At column 0, not indented
                if re.match(r'^[A-Z]\w*(\(.*?\))?\s*==\s', line) and not re.match(r'^<\d+>', line):
                    return i - 1
                # Top-level CONSTANT/VARIABLE declarations (at column 0, not indented)
                if re.match(r'^(CONSTANT|CONSTANTS|VARIABLE|VARIABLES)\s', line):
                    return i - 1

        i += 1

    return i - 1


def parse_theorems(lines):
    """Parse all theorems/lemmas from TLA+ file lines.

    Returns list of TheoremInfo objects.
    """
    theorems = []
    i = 0

    while i < len(lines):
        line = lines[i].strip()

        # Match theorem/lemma declaration with a name
        m = re.match(r'^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(\w+)\s*==', line)
        if not m:
            # Also match unnamed theorems like "THEOREM Spec => []Inv"
            m2 = re.match(r'^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(.+)', line)
            if m2 and '==' not in line:
                # Unnamed theorem - skip these as they can't be referenced
                i += 1
                continue
            if not m:
                i += 1
                continue

        keyword = m.group(1)
        name = m.group(2)
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
        if re.search(r'\bBY\s', first_line) or re.search(r'\bPROOF\s+BY\s', first_line):
            proof_start = i
            has_proof = True
        elif re.search(r'\bOBVIOUS\s*$', first_line):
            proof_start = i
            has_proof = False
        elif re.search(r'\bOMITTED\s*$', first_line) or re.search(r'\bPROOF\s+OMITTED\s*$', first_line):
            proof_start = i
            has_proof = False

        if proof_start is None:
            j = i + 1
            while j < len(lines):
                sline = lines[j].strip()
                orig = lines[j]

                # End of module
                if re.match(r'^={3,}', sline):
                    break

                # Another top-level theorem/lemma (not indented)
                if re.match(r'^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s', sline) and (not orig or not orig[0].isspace()):
                    break

                # Separator
                if re.match(r'^-{3,}', sline):
                    break

                # Top-level definitions (not indented, at column 0)
                if orig and not orig[0].isspace():
                    if re.match(r'^[A-Z]\w*(\(.*?\))?\s*==\s', sline) and not re.match(r'^<\d+>', sline):
                        break
                    if re.match(r'^(CONSTANT|CONSTANTS|VARIABLE|VARIABLES)\s', sline):
                        break

                # Proof indicators
                if sline == 'PROOF' or re.match(r'^PROOF\s+BY\s', sline):
                    proof_start = j
                    has_proof = True
                    break
                if sline == 'OBVIOUS':
                    proof_start = j
                    has_proof = False
                    break
                if sline == 'OMITTED' or sline == 'PROOF OMITTED':
                    proof_start = j
                    has_proof = False
                    break
                if re.match(r'^<\d+>', sline):
                    proof_start = j
                    has_proof = True
                    break
                # BY at start of line (possibly indented)
                if re.match(r'^\s*BY\s', orig) or sline.startswith('BY ') or sline == 'BY':
                    proof_start = j
                    has_proof = True
                    break

                j += 1

        stmt_end = (proof_start - 1) if proof_start is not None and proof_start > stmt_start else stmt_start

        if proof_start is not None:
            proof_end = find_proof_end(lines, proof_start)
        else:
            proof_end = stmt_end

        # Only include theorems that have actual proofs (not OMITTED/OBVIOUS only)
        if has_proof:
            theorems.append(TheoremInfo(keyword, name, stmt_start, stmt_end, proof_start, proof_end, has_proof))

        i = (proof_end + 1) if proof_end is not None else (j + 1 if proof_start is None else proof_end + 1)
        continue

    return theorems


def extract_preamble(lines, theorems):
    """Extract everything before the first theorem - the preamble (module header, extends, constants, vars, defs)."""
    if not theorems:
        return lines[:]
    return lines[:theorems[0].statement_start]


def get_theorem_statement_lines(lines, thm):
    """Get the statement lines of a theorem (without proof)."""
    # Handle single-line theorem with proof on same line
    if thm.proof_start == thm.statement_start:
        line = lines[thm.statement_start]
        # Remove the BY/OBVIOUS/OMITTED part
        # Find the theorem body by removing proof
        for pat in [r'\s+BY\s+.*$', r'\s+OBVIOUS\s*$', r'\s+OMITTED\s*$', r'\s+PROOF\s+OMITTED\s*$']:
            line = re.sub(pat, '', line)
        return [line]

    result = lines[thm.statement_start:thm.statement_end + 1]
    # Clean trailing empty lines
    while result and result[-1].strip() == '':
        result.pop()
    return result


def merge_files(files_by_module, dep_graph, target_module):
    """Merge all dependencies of target_module into a single content string.

    Returns merged lines and the module name to use.
    """
    all_deps = find_all_deps(target_module, dep_graph)

    if not all_deps:
        # No local dependencies, just return the file content
        with open(files_by_module[target_module], 'r') as f:
            return f.readlines(), target_module

    # Topological order of all deps + target
    order = topo_sort(dep_graph)
    relevant = [m for m in order if m in all_deps or m == target_module]

    # Merge: collect all extends (stdlib only), then all content from each module
    all_extends = set()
    merged_body_lines = []

    for mod in relevant:
        with open(files_by_module[mod], 'r') as f:
            content = f.read()

        mod_lines = content.split('\n')

        # Collect stdlib extends
        for ext in parse_extends(content):
            if ext in STDLIB_MODULES:
                all_extends.add(ext)

        # Extract body (between MODULE header and ending ====)
        body_start = None
        body_end = None
        for idx, line in enumerate(mod_lines):
            if body_start is None and re.match(r'^-+\s*MODULE\s+\w+\s*-+', line.strip()):
                body_start = idx + 1
            if re.match(r'^={3,}', line.strip()):
                body_end = idx

        if body_start is None:
            continue
        if body_end is None:
            body_end = len(mod_lines)

        body = mod_lines[body_start:body_end]

        # Remove EXTENDS line from body (we'll put a unified one)
        filtered_body = []
        for line in body:
            if re.match(r'^EXTENDS\s', line.strip()):
                continue
            # Remove INSTANCE lines that reference local modules we're merging
            inst_match = re.match(r'^(\w+)\s*==\s*INSTANCE\s+(\w+)', line.strip())
            if inst_match and inst_match.group(2) in all_deps:
                continue
            if re.match(r'^INSTANCE\s+(\w+)', line.strip()):
                imod = re.match(r'^INSTANCE\s+(\w+)', line.strip()).group(1)
                if imod in all_deps:
                    continue
            filtered_body.append(line)

        if mod != target_module:
            merged_body_lines.append(f'(* ---- Content from module {mod} ---- *)')
        merged_body_lines.extend(filtered_body)
        if mod != target_module:
            merged_body_lines.append('')

    # Build final content
    header_lines = []
    extends_str = ', '.join(sorted(all_extends)) if all_extends else ''

    # We'll use a placeholder module name; caller will set it
    header_lines.append(f'---- MODULE __PLACEHOLDER__ ----')
    if extends_str:
        header_lines.append(f'EXTENDS {extends_str}')

    result_lines = header_lines + merged_body_lines + ['=' * 40]
    return [l + '\n' for l in result_lines], target_module


def generate_benchmark_file(lines_or_content, theorems, target_idx, module_name, benchmark_name):
    """Generate a benchmark file for the target_idx-th theorem.

    - All theorems before target_idx: keep statement, add PROOF OMITTED
    - Target theorem: keep statement, remove proof entirely
    - All theorems after target_idx: removed entirely
    """
    if isinstance(lines_or_content, str):
        lines = lines_or_content.split('\n')
    else:
        lines = [l.rstrip('\n') for l in lines_or_content]

    target_thm = theorems[target_idx]

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
                result.extend(stmt_lines)
                result.append('  PROOF OMITTED')
                result.append('')
            elif found_thm == target_idx:
                # Target theorem: replace proof with OBVIOUS (will fail for non-trivial theorems)
                result.extend(stmt_lines)
                result.append('PROOF OBVIOUS')
                result.append('')
            else:
                # Theorems after target: skip entirely
                pass

            # Skip past the theorem's proof
            end = thm.proof_end if thm.proof_end is not None else thm.statement_end
            i = end + 1
            continue

        # Check if this line is inside a theorem range (shouldn't happen, but safety)
        inside = False
        for idx, (start, end) in thm_ranges.items():
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
                if re.match(r'^={3,}', lines[i].strip()):
                    result.append(lines[i])
                i += 1
                continue
            result.append(lines[i])

        i += 1

    # Ensure module ends with ====
    if not any(re.match(r'^={3,}', l.strip()) for l in result[-3:] if l.strip()):
        result.append('=' * 40)

    # Replace module name in header
    final = []
    for line in result:
        if re.match(r'^-+\s*MODULE\s+\w+\s*-+', line.strip()):
            line = re.sub(r'MODULE\s+\w+', f'MODULE {benchmark_name}', line)
        if '__PLACEHOLDER__' in line:
            line = line.replace('__PLACEHOLDER__', benchmark_name)
        final.append(line)

    return '\n'.join(final)


def process_module_dir(module_dir_name):
    """Process a single module directory and generate benchmarks."""
    module_path = os.path.join(SOURCE_ROOT, module_dir_name)
    tla_files = find_tla_files(module_path)

    if not tla_files:
        return 0

    # Build module -> filepath mapping
    files_by_module = {}
    for f in tla_files:
        with open(f, 'r') as fh:
            content = fh.read()
        mod_name = parse_module_name(content)
        if mod_name:
            files_by_module[mod_name] = f

    # Build dependency graph
    dep_graph = build_dependency_graph(files_by_module)

    # For each file, determine if it needs merging
    # A file needs merging if it has local dependencies
    benchmark_count = 0
    out_dir = os.path.join(BENCHMARK_DIR, module_dir_name)

    for mod_name, filepath in files_by_module.items():
        with open(filepath, 'r') as f:
            content = f.read()

        raw_lines = content.split('\n')
        theorems = parse_theorems(raw_lines)

        if not theorems:
            continue

        # Check if this module has local dependencies
        local_deps = find_all_deps(mod_name, dep_graph)

        if local_deps:
            # Merge all dependencies into single content
            merged_lines, _ = merge_files(files_by_module, dep_graph, mod_name)
            work_lines = [l.rstrip('\n') for l in merged_lines]
            # Re-parse theorems from merged content
            theorems = parse_theorems(work_lines)
            if not theorems:
                continue
        else:
            work_lines = raw_lines

        # Generate one benchmark file per theorem
        source_basename = os.path.splitext(os.path.basename(filepath))[0]

        # Track used names to handle duplicates
        name_counts = {}
        for idx, thm in enumerate(theorems):
            base_name = f'{source_basename}_{thm.name}'
            if base_name in name_counts:
                name_counts[base_name] += 1
                benchmark_name = f'{base_name}_{name_counts[base_name]}'
            else:
                name_counts[base_name] = 0
                benchmark_name = base_name
            benchmark_file = os.path.join(out_dir, f'{benchmark_name}.tla')

            os.makedirs(out_dir, exist_ok=True)

            content = generate_benchmark_file(work_lines, theorems, idx, mod_name, benchmark_name)

            with open(benchmark_file, 'w') as f:
                f.write(content)

            benchmark_count += 1
            print(f'  Generated: {os.path.relpath(benchmark_file, SOURCE_ROOT)}')

    return benchmark_count


def main():
    # Clean benchmark dir
    if os.path.exists(BENCHMARK_DIR):
        import shutil
        shutil.rmtree(BENCHMARK_DIR)
    os.makedirs(BENCHMARK_DIR, exist_ok=True)

    module_dirs = find_source_dirs()
    total = 0

    for mod_dir in module_dirs:
        print(f'\nProcessing {mod_dir}/')
        count = process_module_dir(mod_dir)
        total += count
        if count:
            print(f'  -> {count} benchmarks')

    print(f'\nTotal benchmarks generated: {total}')


if __name__ == '__main__':
    main()
