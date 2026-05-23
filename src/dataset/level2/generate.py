#!/usr/bin/env python3
"""Generate Level 2 benchmarks from source .tla files.

Core principle (from src/level2/design.md):
  Keep the model and the statement of the top-level theorem;
  delete all proof content.

For each top-level THEOREM in source/<Module>/<File>.tla we emit one
file benchmark/level2/<Module>/<File>_<TheoremName>.tla in which:
  - The module + EXTENDS + CONSTANT/VARIABLE/ASSUME/AXIOM + all `==`
    definitions are kept verbatim.
  - All other THEOREMs and all LEMMAs (statement + proof) are deleted.
  - The target THEOREM's proof body is replaced with `PROOF OBVIOUS`.
  - INSTANCE-target .tla files are copied alongside with all their
    proofs stripped (`PROOF OMITTED`).

Top-level selection (OR rule, applied to THEOREM-keyword decls only):
  1. Unnamed rule: T has no name (TLA+ syntax can't reference it → standalone).
  2. Shape rule:   statement is `<S> => ...` where `<S>` is a spec formula.
  3. Graph rule:   T has a name and no other theorem references it.

Post-selection filters:
  A. Manual-proof filter: drop candidates whose source has no structured
     TLAPS proof (bare statement / PROOF OMITTED / PROOF OBVIOUS). L2's
     contract is "AI writes a proof, compared against a human reference",
     so candidates without ground truth are out of scope for now.
     Known cost: PaxosTuple.tla:79 `Spec => V!Spec` (proof lives in the
     companion file PaxosProof.tla) and PConProof.tla:520
     `Spec => [](chosen = V!chosen)` (model-checked by TLC, no TLAPS
     proof written). Both are genuine main theorems; they can be revived
     later in a separate "no-reference-proof" track if we ever want it.
  B. Within-file dedup: collapse exact-text-duplicate statements. Catches
     Peterson.tla L124/L134/L183 — three identical
     `THEOREM Spec => []MutualExclusion` decls the author wrote to
     showcase different prover backends; as L2 prompts they are
     indistinguishable, so keep the first by line.
  C. Cross-directory dedup: across all output directories, collapse
     byte-identical target benchmarks. Catches the seven `Sets_*.tla`
     pairs that arise because source/Consensus/Sets.tla and
     source/Data/Sets.tla are near-identical copies of the same
     utility library (only two prover-hint lines differ, both inside
     proof bodies that L2 strips, so the emitted L2 prompts are
     byte-identical). When duplicates are detected, the copy under
     `Data/` is kept (utility libraries are at home in `Data/`); the
     copies in other directories are removed and the audit log records
     each drop. Dep files (e.g. `Sets.tla` itself, copied alongside
     targets) are not subject to this pass — they may legitimately need
     to live in multiple directories because other targets in those
     directories depend on them.

Spec formulas are identified by SANY-AST shape (see src/dataset/sany-dump/),
not by name match. The audit log flags non-`Spec` names, zero specs,
multiple specs, multiple top-level theorems, unnamed top-levels, and
every drop made by filters A, B, and C.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
SOURCE_ROOT = os.path.join(PROJECT_ROOT, 'source')
BENCHMARK_DIR = os.path.join(PROJECT_ROOT, 'benchmark', 'level2')
SANY_DUMP = os.path.join(PROJECT_ROOT, 'src', 'dataset', 'sany-dump', 'run.sh')

# Reuse L1's proof-stripping logic for dependency .tla copies.
sys.path.insert(0, os.path.join(PROJECT_ROOT, 'src', 'dataset', 'level1'))
from generate import (  # noqa: E402
    parse_theorems, strip_all_proofs, parse_extends, parse_instances, STDLIB_MODULES,
)

KEYWORD_PATTERN = re.compile(r'^\s*(THEOREM|LEMMA|AXIOM|COROLLARY|PROPOSITION)\b')
MODULE_HEADER = re.compile(r'^(-+\s*MODULE\s+)(\w+)(\s*-+)')


def dump_sany(tla_path):
    res = subprocess.run([SANY_DUMP, tla_path], capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(
            f"SANY dump failed for {tla_path}:\n--stdout--\n{res.stdout}\n--stderr--\n{res.stderr}"
        )
    # SANY's PlusCal label-adder and parse-error reporter print to System.out
    # from inside frontEndMain. Skip past the sentinel marker we print in
    # DumpSemantics.java to find the actual JSON.
    marker = '--- BEGIN SANY-DUMP JSON ---'
    idx = res.stdout.find(marker)
    if idx < 0:
        raise RuntimeError(f"SANY produced no JSON for {tla_path}:\n{res.stdout!r}\nstderr:\n{res.stderr}")
    return json.loads(res.stdout[idx + len(marker):])


def determine_keyword(lines, line_start):
    """Read source at line_start (1-indexed) and return the leading keyword."""
    if not (1 <= line_start <= len(lines)):
        return None
    m = KEYWORD_PATTERN.match(lines[line_start - 1])
    return m.group(1) if m else None


def find_top_level(theorems, spec_formulas):
    """Top-level iff any of:
      - unnamed: T has no name (TLA+ syntax can't reference it → it can't
        be a helper; it must be a standalone claim by the author's intent).
      - shape:   T's statement is `<S> => ...` where <S> is a spec formula.
      - graph:   T has a name and no other theorem references it.

    Returns (theorem_dict, by_unnamed, by_shape, by_graph) tuples.
    """
    incoming = {}
    for t in theorems:
        if t['name']:
            incoming.setdefault(t['name'], set())
    for t in theorems:
        src_name = t['name'] or f"__unnamed_{t['loc']['line_start']}"
        for ref in t['references']:
            if ref in incoming:
                incoming[ref].add(src_name)

    out = []
    for t in theorems:
        unnamed_match = not t['name']
        shape_match = (t['shape']['kind'] == 'implies'
                       and t['shape']['lhs_spec_ref'] in spec_formulas)
        graph_match = (not unnamed_match
                       and len(incoming.get(t['name'], set())) == 0)
        if unnamed_match or shape_match or graph_match:
            out.append((t, unnamed_match, shape_match, graph_match))
    return out


def _statement_text(target_thm, source_lines):
    """Extract the statement portion of a THEOREM (everything before its proof body).

    SANY's `loc` for a TheoremNode spans the whole `THEOREM ... <proof>` range,
    so we trim off the proof using `proof_loc.line_start - 1`. If there is no
    proof, the statement runs to `loc.line_end`. Returned text is the joined
    source lines, stripped of surrounding whitespace.
    """
    loc = target_thm['loc']
    ploc = target_thm.get('proof_loc')
    if ploc and ploc.get('line_start', -1) > 0:
        end_line = ploc['line_start'] - 1
    else:
        end_line = loc['line_end']
    return ''.join(source_lines[loc['line_start'] - 1 : end_line]).strip()


def _has_manual_proof(target_thm, source_lines):
    """Return True iff the source has a structured TLAPS proof body.

    Returns False for:
      - no proof body at all (SANY emits no `proof_loc`, e.g. PConProof.tla L505)
      - `PROOF OMITTED` / `OMITTED` placeholder
      - `PROOF OBVIOUS` / `OBVIOUS` placeholder

    All other proof bodies (a `<N>` proof tree, a `BY ...` leaf, a `PROOF BY`
    line, etc.) count as manual proofs.
    """
    ploc = target_thm.get('proof_loc')
    if not (ploc and ploc.get('line_start', -1) > 0):
        return False
    body = ''.join(source_lines[ploc['line_start'] - 1 : ploc['line_end']]).strip()
    if body.startswith('PROOF'):
        body = body[5:].lstrip()
    return body not in ('OMITTED', 'OBVIOUS')


def target_theorem_name(theorem):
    """Pick a name string used for the benchmark filename.

    Returns (name, was_sanitized). If the RHS primary name carries an INSTANCE
    namespace separator `!` (e.g. `V!Spec`), it is replaced with `_` because
    `!` is not legal in a TLA+ module identifier.
    """
    if theorem['name']:
        return theorem['name'], False
    rhs = theorem['shape'].get('rhs_primary_name')
    if rhs:
        sanitized = rhs.replace('!', '_')
        return sanitized, sanitized != rhs
    return f"line{theorem['loc']['line_start']}", False


def apply_edits(lines, edits):
    """Apply (start_line, end_line, replacement_text) edits.

    Lines are 1-indexed, inclusive. Edits must not overlap. The replacement
    text replaces the entire range; lines outside any range are emitted
    unchanged.
    """
    edits = sorted(edits, key=lambda e: e[0])
    for i in range(len(edits) - 1):
        if edits[i][1] >= edits[i + 1][0]:
            raise ValueError(f"Overlapping edits: {edits[i]} and {edits[i + 1]}")
    out = []
    cursor = 1
    for start, end, repl in edits:
        if start > cursor:
            out.extend(lines[cursor - 1:start - 1])
        if repl:
            out.append(repl)
        cursor = end + 1
    if cursor <= len(lines):
        out.extend(lines[cursor - 1:])
    return ''.join(out)


def build_benchmark(source_lines, dump, target_thm, benchmark_module_name):
    """Build the benchmark .tla text by editing source_lines."""
    edits = []
    target_id = id(target_thm)
    for t in dump['theorems']:
        if id(t) == target_id:
            ploc = t.get('proof_loc')
            # Filter A in process_file guarantees the target has a real proof body.
            assert ploc and ploc.get('line_start', -1) > 0, (
                f"build_benchmark invoked on target without proof body at "
                f"{source_lines[t['loc']['line_start'] - 1].rstrip()!r}; "
                "should have been filtered upstream."
            )
            edits.append((ploc['line_start'], ploc['line_end'], 'PROOF OBVIOUS\n'))
        else:
            # Delete other theorems/lemmas entirely.
            loc = t['loc']
            edits.append((loc['line_start'], loc['line_end'], ''))

    text = apply_edits(source_lines, edits)

    # Rename module header to the benchmark module name.
    out_lines = text.splitlines(keepends=True)
    for i, line in enumerate(out_lines):
        m = MODULE_HEADER.match(line)
        if m:
            out_lines[i] = f"{m.group(1)}{benchmark_module_name}{m.group(3)}\n"
            break
    return ''.join(out_lines)


def _gather_local_deps(start_mods, src_dir):
    """Transitively collect local-module deps (EXTENDS + INSTANCE) starting
    from `start_mods`. Standard-library modules are excluded.

    Returns a list of (module_name, .tla path) pairs in BFS discovery order.
    """
    out = []
    seen = set()
    queue = list(start_mods)
    while queue:
        mod = queue.pop(0)
        if not mod or mod in seen or mod in STDLIB_MODULES:
            continue
        dep_path = os.path.join(src_dir, f"{mod}.tla")
        if not os.path.isfile(dep_path):
            continue
        seen.add(mod)
        out.append((mod, dep_path))
        with open(dep_path, encoding='utf-8') as f:
            dep_content = f.read()
        for ext in parse_extends(dep_content):
            if ext not in STDLIB_MODULES and ext not in seen:
                queue.append(ext)
        for _, inst_mod in parse_instances(dep_content):
            if inst_mod not in seen:
                queue.append(inst_mod)
    return out


def copy_deps(dump, source_path, out_dir):
    """Copy every local-module dep of `source_path` into `out_dir`, with all
    proofs stripped to PROOF OMITTED. Covers both EXTENDS (e.g. EuclidEx -> GCD)
    and INSTANCE (e.g. Paxos -> Consensus) references, transitively.

    Returns the list of copied basenames.
    """
    src_dir = os.path.dirname(os.path.abspath(source_path))
    direct_deps = []
    for ext in dump.get('extends', []):
        if ext not in STDLIB_MODULES:
            direct_deps.append(ext)
    for inst in dump.get('instances', []):
        mod = inst.get('module')
        if mod:
            direct_deps.append(mod)

    copied = []
    for mod, dep_path in _gather_local_deps(direct_deps, src_dir):
        with open(dep_path, encoding='utf-8') as f:
            dep_text = f.read()
        dep_lines = dep_text.split('\n')
        dep_thms = parse_theorems(dep_lines)
        dest = os.path.join(out_dir, os.path.basename(dep_path))
        if dep_thms:
            stripped = strip_all_proofs(dep_lines, dep_thms)
            with open(dest, 'w', encoding='utf-8') as f:
                f.write(stripped if stripped.endswith('\n') else stripped + '\n')
        else:
            shutil.copy2(dep_path, dest)
        copied.append(os.path.basename(dep_path))
    return copied


def cross_dir_dedup(target_paths, audit_writer, preferred_dir='Data'):
    """Filter C — drop target benchmarks that are byte-identical to a target
    in another output directory.

    When duplicates exist we keep the copy under `preferred_dir` (default
    `Data` — the natural home for utility-library benchmarks); if no copy
    is under `preferred_dir`, the alphabetically-first path wins. The
    other copies are deleted and every drop is recorded in the audit log.

    Returns the number of files removed.
    """
    import hashlib
    by_hash = {}
    for path in target_paths:
        with open(path, 'rb') as f:
            h = hashlib.sha256(f.read()).hexdigest()
        by_hash.setdefault(h, []).append(path)

    sep = os.sep
    preferred_marker = f"{sep}{preferred_dir}{sep}"
    removed = 0
    for group in by_hash.values():
        if len(group) < 2:
            continue
        preferred = sorted(p for p in group if preferred_marker in p)
        keeper = preferred[0] if preferred else sorted(group)[0]
        for path in group:
            if path == keeper:
                continue
            os.remove(path)
            audit_writer.write(
                f"[level2-audit] {os.path.relpath(path, PROJECT_ROOT)}: "
                f"byte-identical to {os.path.relpath(keeper, PROJECT_ROOT)} "
                f"— removed (filter C, cross-dir dedup)\n"
            )
            removed += 1
    return removed


def process_file(source_path, audit_writer, output_root, module_subdir=None,
                 generated_paths=None):
    """Generate L2 benchmarks for one source .tla file. Returns count emitted.

    If `generated_paths` is a list, each generated target benchmark path is
    appended to it (for downstream cross-directory dedup).
    """
    with open(source_path, encoding='utf-8') as f:
        text = f.read()
    source_lines = text.splitlines(keepends=True)

    try:
        dump = dump_sany(source_path)
    except RuntimeError as e:
        audit_writer.write(f"[level2-audit] {source_path}: SANY parse failed — {e}\n")
        return 0

    module = dump['module']
    spec_formulas = set(dump['spec_formulas'])

    if not spec_formulas:
        audit_writer.write(
            f"[level2-audit] {source_path}: no spec formula identified — shape rule will not match\n"
        )
    elif len(spec_formulas) > 1:
        audit_writer.write(
            f"[level2-audit] {source_path}: multiple spec formulas: {sorted(spec_formulas)}\n"
        )
    elif 'Spec' not in spec_formulas:
        only = next(iter(spec_formulas))
        audit_writer.write(
            f"[level2-audit] {source_path}: identified spec formula `{only}` — name != `Spec`\n"
        )

    for t in dump['theorems']:
        t['_keyword'] = determine_keyword(source_lines, t['loc']['line_start'])

    theorem_candidates = [t for t in dump['theorems'] if t['_keyword'] == 'THEOREM']
    top_level = find_top_level(theorem_candidates, spec_formulas)

    # Filter A — require a manual TLAPS proof in the source.
    # See module docstring for the rationale and the two known-dropped main
    # theorems. We treat PROOF OMITTED and PROOF OBVIOUS as "no manual proof"
    # because both leave nothing for AI to compare against (OMITTED is an
    # explicit deferral; OBVIOUS is a 1-token placeholder that passes
    # trivially and so carries no benchmark signal).
    survivors = []
    for entry in top_level:
        target_thm = entry[0]
        if _has_manual_proof(target_thm, source_lines):
            survivors.append(entry)
        else:
            line = target_thm['loc']['line_start']
            name = target_thm['name'] or f"<unnamed L{line}>"
            audit_writer.write(
                f"[level2-audit] {source_path}: top-level THEOREM {name} at line "
                f"{line} has no manual TLAPS proof body — skipped (filter A)\n"
            )
    top_level = survivors

    # Filter B — within-file exact-text statement dedup. Keep first by line.
    seen_stmts = {}
    deduped = []
    for entry in top_level:
        target_thm = entry[0]
        stmt = _statement_text(target_thm, source_lines)
        if stmt in seen_stmts:
            line = target_thm['loc']['line_start']
            kept_line = seen_stmts[stmt]
            name = target_thm['name'] or f"<unnamed L{line}>"
            audit_writer.write(
                f"[level2-audit] {source_path}: top-level THEOREM {name} at line "
                f"{line} has identical statement text to candidate kept at line "
                f"{kept_line} — skipped (filter B)\n"
            )
        else:
            seen_stmts[stmt] = target_thm['loc']['line_start']
            deduped.append(entry)
    top_level = deduped

    if not top_level:
        audit_writer.write(
            f"[level2-audit] {source_path}: no top-level THEOREM identified — no benchmarks generated\n"
        )
        return 0
    if len(top_level) > 1:
        names = []
        for t, unnamed, shp, grph in top_level:
            label = t['name'] or f"<unnamed L{t['loc']['line_start']}>"
            if unnamed:
                tag = "[unnamed]"
            else:
                tag = f"[shape={'Y' if shp else 'N'}/graph={'Y' if grph else 'N'}]"
            names.append(label + tag)
        audit_writer.write(
            f"[level2-audit] {source_path}: multiple top-level THEOREMs: {names}\n"
        )

    out_dir = os.path.join(output_root, module_subdir or module)
    os.makedirs(out_dir, exist_ok=True)

    base_module = os.path.splitext(os.path.basename(source_path))[0]
    used_names = set()
    count = 0
    for target_thm, _, _, _ in top_level:
        if not target_thm['name']:
            # Not a warning: unnamed THEOREMs are top-level by construction.
            # This entry just records how the filename was derived.
            line = target_thm['loc']['line_start']
            rhs = target_thm['shape'].get('rhs_primary_name')
            if rhs:
                audit_writer.write(
                    f"[level2-audit] {source_path}: unnamed top-level THEOREM at line "
                    f"{line} — filename derived from rhs primary name `{rhs}`\n"
                )
            else:
                audit_writer.write(
                    f"[level2-audit] {source_path}: unnamed top-level THEOREM at line "
                    f"{line} — no usable rhs primary name; filename uses line "
                    f"number `line{line}`\n"
                )
        thm_name, sanitized = target_theorem_name(target_thm)
        if sanitized:
            audit_writer.write(
                f"[level2-audit] {source_path}: rhs primary name "
                f"`{target_thm['shape'].get('rhs_primary_name')}` contains `!` "
                f"(INSTANCE namespace separator); sanitized to `{thm_name}` for module identifier\n"
            )
        bench_module_name = f"{base_module}_{thm_name}"
        # Disambiguate filename collisions (e.g. Peterson.tla has 3 unnamed
        # `THEOREM Spec => []MutualExclusion` lines that all map to the same name).
        if bench_module_name in used_names:
            bench_module_name = f"{bench_module_name}_L{target_thm['loc']['line_start']}"
            audit_writer.write(
                f"[level2-audit] {source_path}: filename collision on `{base_module}_{thm_name}`, "
                f"disambiguated to `{bench_module_name}`\n"
            )
        used_names.add(bench_module_name)
        bench_file = os.path.join(out_dir, f"{bench_module_name}.tla")

        bench_text = build_benchmark(source_lines, dump, target_thm, bench_module_name)
        with open(bench_file, 'w', encoding='utf-8') as f:
            f.write(bench_text)
        copy_deps(dump, source_path, out_dir)
        count += 1
        if generated_paths is not None:
            generated_paths.append(bench_file)
        print(f"  generated: {os.path.relpath(bench_file, PROJECT_ROOT)}")

    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', default=SOURCE_ROOT,
                        help='Directory of source .tla files (default: %(default)s)')
    parser.add_argument('--output-dir', default=BENCHMARK_DIR,
                        help='Output directory for benchmarks (default: %(default)s)')
    parser.add_argument('--filter', default=None,
                        help='Glob-ish substring to limit which source files we process')
    parser.add_argument('files', nargs='*',
                        help='Specific .tla files to process (overrides --source-dir scan)')
    args = parser.parse_args()

    output_root = os.path.abspath(args.output_dir)
    os.makedirs(output_root, exist_ok=True)
    audit_path = os.path.join(output_root, 'audit.log')

    if args.files:
        targets = [(os.path.abspath(p), None) for p in args.files]
    else:
        src_root = os.path.abspath(args.source_dir)
        targets = []
        for root, _, files in os.walk(src_root):
            if '.tlaps' in root:
                continue
            for fname in sorted(files):
                if not fname.endswith('.tla'):
                    continue
                full = os.path.join(root, fname)
                if args.filter and args.filter not in full:
                    continue
                subdir = os.path.relpath(root, src_root).split(os.sep)[0]
                if subdir == '.':
                    subdir = os.path.splitext(fname)[0]
                targets.append((full, subdir))

    total = 0
    generated_paths = []
    with open(audit_path, 'w', encoding='utf-8') as audit_writer:
        for path, subdir in targets:
            print(f"\nProcessing {os.path.relpath(path, PROJECT_ROOT)}")
            try:
                total += process_file(path, audit_writer, output_root,
                                      module_subdir=subdir,
                                      generated_paths=generated_paths)
            except Exception as e:
                audit_writer.write(f"[level2-audit] {path}: ERROR {e!r}\n")
                print(f"  ERROR: {e}", file=sys.stderr)
        removed = cross_dir_dedup(generated_paths, audit_writer)

    print(f"\nTotal L2 benchmarks: {total - removed} ({total} generated, {removed} removed by cross-dir dedup)")
    print(f"Audit log: {os.path.relpath(audit_path, PROJECT_ROOT)}")


if __name__ == '__main__':
    main()
