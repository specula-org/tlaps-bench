#!/usr/bin/env python3
"""Generate Level 2 benchmarks from source .tla files.

Core principle (strict L2, from src/dataset/level2/design.md, Issue #1/#3):
  Keep only what is needed to STATE the top-level theorem; delete every
  other definition, all other theorems/lemmas, all proof content, and all
  comments. The AI must rediscover the inductive invariant and design the
  proof structure from scratch.

For each top-level THEOREM in source/<Module>/<File>.tla we emit one
file benchmark/level2/<Module>/<File>_<TheoremName>.tla in which:
  - The module + EXTENDS + CONSTANT/VARIABLE/ASSUME/AXIOM are kept.
  - Only the `==` definitions / named INSTANCE bindings reachable from the
    target theorem's STATEMENT (transitive closure over the definition-
    dependency graph, seeded by the statement + kept ASSUME/AXIOM) survive;
    unreachable ones (inductive invariants like `Inv`/`TypeOK`, helper
    operators like `SafeAt`/`MsgInv`) are deleted as proof artifacts.
    When the goal IS an invariant (`Spec => []Inv`), that invariant is in
    the statement, so it is reachable and kept — the goal can't be hidden.
  - All other THEOREMs and all LEMMAs (statement + proof) are deleted.
  - The target THEOREM's proof body is replaced with `PROOF OBVIOUS`.
  - All comments (`\\*` line, `(* … *)` block) are stripped.
  - Dep .tla files (EXTENDS, or kept INSTANCEs) are copied alongside with
    their proofs stripped (`PROOF OMITTED`) and comments stripped.

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
  A'. Known-false filter: drop a top-level theorem whose goal TLC has shown
     to be FALSE, even though the source "proves" it via an OMITTED sub-step
     that papers over the gap (e.g. PaxosProof StructOK3). A false goal admits
     no honest proof, so it cannot be a benchmark. This is now the ONLY reason
     an OMITTED-sub-step theorem is dropped: every other such theorem is a
     published/verified result and is KEPT as a (hard) from-scratch benchmark,
     since L2 grades by tlapm rather than by the human reference proof.
     See KNOWN_FALSE_TARGETS for the per-target TLC evidence.
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
import subprocess
import sys

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
SOURCE_ROOT = os.path.join(PROJECT_ROOT, "source")
BENCHMARK_DIR = os.path.join(PROJECT_ROOT, "benchmark", "level2")
SANY_DUMP = os.path.join(PROJECT_ROOT, "src", "dataset", "sany-dump", "run.sh")

# Reuse L1's proof-stripping logic for dependency .tla copies.
sys.path.insert(0, os.path.join(PROJECT_ROOT, "src", "dataset", "level1"))
from generate import (  # noqa: E402
    STDLIB_MODULES,
    parse_extends,
    parse_instances,
    parse_theorems,
    strip_all_proofs,
)

KEYWORD_PATTERN = re.compile(r"^\s*(THEOREM|LEMMA|AXIOM|COROLLARY|PROPOSITION)\b")
MODULE_HEADER = re.compile(r"^(-+\s*MODULE\s+)(\w+)(\s*-+)")

# Top-level theorems whose goal is actually FALSE — TLC finds a counterexample —
# even though the source "proves" them with an OMITTED sub-step that papers over
# the gap. A false goal admits no honest proof (an agent can only pass it by
# cheating), so it must never become a benchmark. Keyed by
# (source-module basename, target name); each entry is justified by a TLC run.
# This is the *only* reason filter A' now drops an OMITTED-sub-step theorem —
# every other such theorem is a published, verified result and is kept.
KNOWN_FALSE_TARGETS = {
    ("PaxosProof", "StructOK3"): "TLC counterexample: PaxosTuple.tla Phase2a's uniqueness guard tests "
    "m[3] (the value field) instead of m[2] (the ballot), so a single ballot "
    "can carry two distinct 2a values, violating StructOK3's one-value-per-"
    "ballot conjunct. The author commented StructOK3 out of the proven "
    "StructOK and left its inductive step PROOF OMITTED.",
}


def dump_sany(tla_path):
    res = subprocess.run([SANY_DUMP, tla_path], capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(f"SANY dump failed for {tla_path}:\n--stdout--\n{res.stdout}\n--stderr--\n{res.stderr}")
    # SANY's PlusCal label-adder and parse-error reporter print to System.out
    # from inside frontEndMain. Skip past the sentinel marker we print in
    # DumpSemantics.java to find the actual JSON.
    marker = "--- BEGIN SANY-DUMP JSON ---"
    idx = res.stdout.find(marker)
    if idx < 0:
        raise RuntimeError(f"SANY produced no JSON for {tla_path}:\n{res.stdout!r}\nstderr:\n{res.stderr}")
    return json.loads(res.stdout[idx + len(marker) :])


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
        if t["name"]:
            incoming.setdefault(t["name"], set())
    for t in theorems:
        src_name = t["name"] or f"__unnamed_{t['loc']['line_start']}"
        for ref in t["references"]:
            if ref in incoming:
                incoming[ref].add(src_name)

    out = []
    for t in theorems:
        unnamed_match = not t["name"]
        shape_match = t["shape"]["kind"] == "implies" and t["shape"]["lhs_spec_ref"] in spec_formulas
        graph_match = not unnamed_match and len(incoming.get(t["name"], set())) == 0
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
    loc = target_thm["loc"]
    ploc = target_thm.get("proof_loc")
    end_line = ploc["line_start"] - 1 if ploc and ploc.get("line_start", -1) > 0 else loc["line_end"]
    return "".join(source_lines[loc["line_start"] - 1 : end_line]).strip()


def _has_manual_proof(target_thm, source_lines):
    """Return True iff the source has a structured TLAPS proof body.

    Returns False for:
      - no proof body at all (SANY emits no `proof_loc`, e.g. PConProof.tla L505)
      - `PROOF OMITTED` / `OMITTED` placeholder
      - `PROOF OBVIOUS` / `OBVIOUS` placeholder

    All other proof bodies (a `<N>` proof tree, a `BY ...` leaf, a `PROOF BY`
    line, etc.) count as manual proofs.
    """
    ploc = target_thm.get("proof_loc")
    if not (ploc and ploc.get("line_start", -1) > 0):
        return False
    body = "".join(source_lines[ploc["line_start"] - 1 : ploc["line_end"]]).strip()
    if body.startswith("PROOF"):
        body = body[5:].lstrip()
    return body not in ("OMITTED", "OBVIOUS")


def _proof_has_omitted_substep(target_thm, source_lines):
    """Return True iff the source proof admits a sub-step with OMITTED.

    A multi-step proof whose top level is structured but which contains an
    `OMITTED` leaf anywhere (e.g. PaxosProof.tla's `THEOREM Spec => []StructOK3`,
    whose inductive step `<1>2` is `PROOF OMITTED`) was NEVER actually verified
    by tlapm — the admitted step papers over a gap, and in the StructOK3 case
    the statement is in fact false (TLC finds a counterexample). Such theorems
    must not become benchmarks: there is no ground truth that the goal is even
    provable, so an honest agent that reports "unprovable" gets marked wrong
    while an unsound proof gets marked right.

    `_has_manual_proof` already rejects a proof that is *entirely* OMITTED; this
    catches the subtler case of an OMITTED leaf inside an otherwise-structured
    proof. Matches the OMITTED keyword on word boundaries.
    """
    ploc = target_thm.get("proof_loc")
    if not (ploc and ploc.get("line_start", -1) > 0):
        return False
    body = "".join(source_lines[ploc["line_start"] - 1 : ploc["line_end"]])
    return re.search(r"\bOMITTED\b", body) is not None


def target_theorem_name(theorem):
    """Pick a name string used for the benchmark filename.

    Returns (name, was_sanitized). If the RHS primary name carries an INSTANCE
    namespace separator `!` (e.g. `V!Spec`), it is replaced with `_` because
    `!` is not legal in a TLA+ module identifier.
    """
    if theorem["name"]:
        return theorem["name"], False
    rhs = theorem["shape"].get("rhs_primary_name")
    if rhs:
        sanitized = rhs.replace("!", "_")
        return sanitized, sanitized != rhs
    return f"line{theorem['loc']['line_start']}", False


def compute_reachable(dump, target_thm):
    """Names of `==` definitions / INSTANCE bindings needed to STATE the target.

    Seeds from the target theorem's statement references plus every kept
    ASSUME/AXIOM (the model's hypotheses), then takes the transitive closure
    over the definition-dependency graph (operator + instance `references`
    emitted by the SANY dumper). Everything NOT in the returned set is a proof
    artifact (inductive invariant, helper lemma/operator) and is stripped.

    Note the target's *proof* references are deliberately excluded: the proof is
    replaced by `PROOF OBVIOUS`, so any definition used only inside it is gone.
    For `Spec => []Inv` targets, `Inv` is in the statement, so it (and its
    decomposition) is reachable and kept — the goal cannot be hidden.
    """
    adj = {}
    for o in dump["operators"]:
        adj.setdefault(o["name"], set()).update(o.get("references", []))
    for i in dump["instances"]:
        if i.get("name"):
            adj.setdefault(i["name"], set()).update(i.get("references", []))

    seed = set(target_thm.get("statement_references", []))
    for a in dump["assumes"]:
        seed.update(a.get("references", []))

    reachable = set()
    stack = list(seed)
    while stack:
        name = stack.pop()
        if name in reachable:
            continue
        reachable.add(name)
        stack.extend(r for r in adj.get(name, ()) if r not in reachable)
    return reachable


def strip_comments(text):
    """Remove every TLA+ comment from `text`, preserving line structure.

    Handles `\\*` line comments and nested `(* ... *)` block comments, and skips
    comment markers that appear inside string literals. Newlines are always
    preserved so source line geometry (and the `---- MODULE` / `====` lines)
    survives. Stripping comments is what removes residual strategy hints — e.g.
    EWD840's "Dijkstra's invariant" banner and the trailing "here is a more
    detailed, hierarchical proof" note left over from a deleted proof.
    """
    out = []
    i = 0
    n = len(text)
    depth = 0  # block-comment nesting depth
    in_line = False  # inside a \* line comment
    in_str = False  # inside a "..." string literal
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if c == "\n":
                in_line = False
                out.append(c)
            i += 1
        elif depth > 0:
            if c == "(" and nxt == "*":
                depth += 1
                i += 2
            elif c == "*" and nxt == ")":
                depth -= 1
                i += 2
            elif c == "\n":
                out.append(c)  # keep blank line where the comment sat
                i += 1
            else:
                i += 1
        elif in_str:
            out.append(c)
            if c == "\\" and nxt:
                out.append(nxt)
                i += 2
            else:
                if c == '"':
                    in_str = False
                i += 1
        else:
            if c == "\\" and nxt == "*":
                in_line = True
                i += 2
            elif c == "(" and nxt == "*":
                depth = 1
                i += 2
            elif c == '"':
                in_str = True
                out.append(c)
                i += 1
            else:
                out.append(c)
                i += 1
    return "".join(out)


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
            out.extend(lines[cursor - 1 : start - 1])
        if repl:
            out.append(repl)
        cursor = end + 1
    if cursor <= len(lines):
        out.extend(lines[cursor - 1 :])
    return "".join(out)


def build_benchmark(source_lines, dump, target_thm, benchmark_module_name, reachable):
    """Build the benchmark .tla text by editing source_lines.

    Strict L2 (per Issue #1 / #3): keep only the model + target property + the
    bare THEOREM statement; strip every proof artifact. Concretely we:
      - replace the target theorem's proof body with `PROOF OBVIOUS`,
      - delete all other THEOREM/LEMMA declarations,
      - delete every `==` definition / named INSTANCE not in `reachable`
        (the closure of definitions needed to state the goal) — this is what
        removes the inductive invariant `Inv`, `TypeOK`, `MsgInv`, `SafeAt`, …,
      - strip all comments, and tidy the resulting blank-line runs.
    """
    edits = []
    target_id = id(target_thm)
    for t in dump["theorems"]:
        if id(t) == target_id:
            ploc = t.get("proof_loc")
            # Filter A in process_file guarantees the target has a real proof body.
            assert ploc and ploc.get("line_start", -1) > 0, (
                f"build_benchmark invoked on target without proof body at "
                f"{source_lines[t['loc']['line_start'] - 1].rstrip()!r}; "
                "should have been filtered upstream."
            )
            edits.append((ploc["line_start"], ploc["line_end"], "PROOF OBVIOUS\n"))
        else:
            # Delete other theorems/lemmas entirely.
            loc = t["loc"]
            edits.append((loc["line_start"], loc["line_end"], ""))

    # Delete operator definitions not reachable from the target statement —
    # the inductive invariants and helper operators the AI must rediscover.
    for o in dump["operators"]:
        if o["name"] not in reachable:
            loc = o["loc"]
            edits.append((loc["line_start"], loc["line_end"], ""))
    # Delete named INSTANCE bindings that aren't needed to state the goal.
    # Unnamed (bare) INSTANCEs import names into scope unqualified and can't be
    # tracked by reachability, so they are always kept.
    for inst in dump["instances"]:
        if inst.get("name") and inst["name"] not in reachable:
            loc = inst["loc"]
            edits.append((loc["line_start"], loc["line_end"], ""))

    text = apply_edits(source_lines, edits)
    text = strip_comments(text)

    # Rename module header to the benchmark module name.
    out_lines = text.splitlines(keepends=True)
    for i, line in enumerate(out_lines):
        m = MODULE_HEADER.match(line)
        if m:
            out_lines[i] = f"{m.group(1)}{benchmark_module_name}{m.group(3)}\n"
            break
    text = "".join(out_lines)

    # Collapse the blank-line runs left behind by deleted defs / stripped
    # comments down to a single blank line.
    text = re.sub(r"\n[ \t]*\n(?:[ \t]*\n)+", "\n\n", text)
    return text


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
        with open(dep_path, encoding="utf-8") as f:
            dep_content = f.read()
        for ext in parse_extends(dep_content):
            if ext not in STDLIB_MODULES and ext not in seen:
                queue.append(ext)
        for _, inst_mod in parse_instances(dep_content):
            if inst_mod not in seen:
                queue.append(inst_mod)
    return out


def copy_deps(dump, source_path, out_dir, reachable):
    """Copy every local-module dep of `source_path` into `out_dir`, with all
    proofs stripped to PROOF OMITTED. Covers both EXTENDS (e.g. EuclidEx -> GCD)
    and INSTANCE (e.g. Paxos -> Consensus) references, transitively.

    EXTENDS deps are always copied (the module is unconditionally in scope).
    A *named* INSTANCE's dep is copied only if that instance binding survived
    reachability stripping — e.g. Consensus.tla is needed by `Spec => C!Spec`
    (Refinement) but not by `Spec => []Consistency` (Consistent), which drops
    the `C` binding. Unnamed INSTANCEs are always copied (always kept).

    Returns the list of copied basenames.
    """
    src_dir = os.path.dirname(os.path.abspath(source_path))
    direct_deps = []
    for ext in dump.get("extends", []):
        if ext not in STDLIB_MODULES:
            direct_deps.append(ext)
    for inst in dump.get("instances", []):
        mod = inst.get("module")
        if not mod:
            continue
        name = inst.get("name")
        if name and name not in reachable:
            continue  # instance was stripped from the benchmark
        direct_deps.append(mod)

    copied = []
    for _mod, dep_path in _gather_local_deps(direct_deps, src_dir):
        with open(dep_path, encoding="utf-8") as f:
            dep_text = f.read()
        dep_lines = dep_text.split("\n")
        dep_thms = parse_theorems(dep_lines)
        dest = os.path.join(out_dir, os.path.basename(dep_path))
        if dep_thms:
            dep_text = strip_all_proofs(dep_lines, dep_thms)
        # Scrub comments here too: a dependency module the AI can read (its
        # THEOREM statements stay, only proofs become OMITTED) would otherwise
        # leak strategy prose just like the main file.
        dep_text = strip_comments(dep_text)
        dep_text = re.sub(r"\n[ \t]*\n(?:[ \t]*\n)+", "\n\n", dep_text)
        with open(dest, "w", encoding="utf-8") as f:
            f.write(dep_text if dep_text.endswith("\n") else dep_text + "\n")
        copied.append(os.path.basename(dep_path))
    return copied


def cross_dir_dedup(target_paths, audit_writer, preferred_dir="Data"):
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
        with open(path, "rb") as f:
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


# ---------------------------------------------------------------------------
# Shared-model emission (closure(Spec) model + EXTENDS tasks). Opt-in via
# --shared-model. De-duplicates the spec that self-contained tasks inline:
# one `<Module>.tla` model per output dir, each spec-based task EXTENDS it. The
# grader already copies co-located *.tla, so EXTENDS resolves with no grader
# change. Certified sound (obligation-set equivalence) — see tmp/split_poc.
# ---------------------------------------------------------------------------
_BARE_DECL = re.compile(r"^[ \t]*(CONSTANTS?|VARIABLES?)[ \t]*,?[ \t]*$", re.M)
_EXTENDS_START = re.compile(r"^EXTENDS\b")


def _model_closure(dump, seed):
    adj = {}
    for o in dump["operators"]:
        adj.setdefault(o["name"], set()).update(o.get("references", []))
    for i in dump["instances"]:
        if i.get("name"):
            adj.setdefault(i["name"], set()).update(i.get("references", []))
    out, stack = set(), list(seed)
    while stack:
        n = stack.pop()
        if n in out:
            continue
        out.add(n)
        stack.extend(r for r in adj.get(n, ()) if r not in out)
    return out


def compute_model_set(dump, targets):
    """Leak-free shared base = closure of the GOAL spec(s) only, intersected
    with every spec-goal's reachable set. Seeded ONLY from the `lhs_spec_ref` of
    emitted targets (NOT all spec_formulas) so an inductive-invariant spec like
    `ISpec`/`LiveSpec` can't drag `Inv` into the model. The intersection drops
    anything a task is meant to hide; what remains is the common state machine,
    provably free of inductive invariants/proofs."""
    spec_formulas = dump.get("spec_formulas", [])
    main_specs = {t["shape"].get("lhs_spec_ref") for t in targets if t["shape"].get("lhs_spec_ref") in spec_formulas}
    if not main_specs:
        return set(), main_specs
    seed = set(main_specs)
    for a in dump["assumes"]:
        seed.update(a.get("references", []))
    reachable = {id(t): compute_reachable(dump, t) for t in targets}
    model = _model_closure(dump, seed)
    for t in targets:
        if t["shape"].get("lhs_spec_ref") in main_specs:
            model &= reachable[id(t)]
    return model, main_specs


def _decl_edits(dump):
    """Delete CONSTANT/VARIABLE/ASSUME declarations (one per distinct loc) —
    they come via EXTENDS in the task/model-extending file."""
    seen, edits = set(), []
    for e in list(dump.get("constants", [])) + list(dump.get("variables", [])) + list(dump.get("assumes", [])):
        loc = e.get("loc")
        if not loc:
            continue
        key = (loc["line_start"], loc["line_end"])
        if key in seen:
            continue
        seen.add(key)
        edits.append((loc["line_start"], loc["line_end"], ""))
    return edits


def _rewrite_extends_line(text, module):
    """Replace the (possibly multi-line) EXTENDS statement with `EXTENDS <module>`."""
    lines = text.split("\n")
    out, i, done = [], 0, False
    while i < len(lines):
        if not done and _EXTENDS_START.match(lines[i]):
            j = i
            while lines[j].rstrip().endswith(","):
                j += 1
            out.append(f"EXTENDS {module}")
            i = j + 1
            done = True
            continue
        out.append(lines[i])
        i += 1
    return "\n".join(out)


def _sm_tidy(text):
    """Drop stranded pure-dash `----` dividers and collapse blank runs."""
    text = re.sub(r"(?m)^-{4,}[ \t]*$\n?", "", text)
    return re.sub(r"\n[ \t]*\n(?:[ \t]*\n)+", "\n\n", text)


def _rename_header(text, new_name):
    # Rename the FIRST `---- MODULE X ----` line wherever it is — a leading blank
    # line or comment can precede it (e.g. BPConProof), so don't require it to be
    # the first output line, else the rename silently no-ops and the task module
    # name collides with the co-located model.
    out, done = [], False
    for line in text.splitlines(keepends=True):
        if not done:
            m = MODULE_HEADER.match(line)
            if m:
                out.append(f"{m.group(1)}{new_name}{m.group(3)}\n")
                done = True
                continue
        out.append(line)
    return "".join(out)


def build_model(source_lines, dump, model_set):
    """Proof-free shared model (delete-from-source, preserves declaration order
    so an ASSUME/AXIOM that references a later operator still resolves)."""
    edits = []
    for t in dump["theorems"]:
        edits.append((t["loc"]["line_start"], t["loc"]["line_end"], ""))
    for o in dump["operators"]:
        if o["name"] not in model_set:
            edits.append((o["loc"]["line_start"], o["loc"]["line_end"], ""))
    for inst in dump["instances"]:
        if inst.get("name") and inst["name"] not in model_set:
            edits.append((inst["loc"]["line_start"], inst["loc"]["line_end"], ""))
    return _sm_tidy(strip_comments(apply_edits(source_lines, edits)))


def build_benchmark_extends(source_lines, dump, target_thm, bench_module_name, reachable, model_set, module):
    """Like build_benchmark, but the spec lives in the EXTENDS'd model: also
    delete model operators + the CONSTANT/VARIABLE/ASSUME decls, and rewrite the
    EXTENDS line to `EXTENDS <module>`."""
    edits = list(_decl_edits(dump))
    tid = id(target_thm)
    for t in dump["theorems"]:
        if id(t) == tid:
            ploc = t["proof_loc"]
            edits.append((ploc["line_start"], ploc["line_end"], "PROOF OBVIOUS\n"))
        else:
            loc = t["loc"]
            edits.append((loc["line_start"], loc["line_end"], ""))
    for o in dump["operators"]:
        if o["name"] in model_set or o["name"] not in reachable:
            edits.append((o["loc"]["line_start"], o["loc"]["line_end"], ""))
    for inst in dump["instances"]:
        if inst.get("name") and (inst["name"] in model_set or inst["name"] not in reachable):
            edits.append((inst["loc"]["line_start"], inst["loc"]["line_end"], ""))
    text = apply_edits(source_lines, edits)
    text = strip_comments(text)
    text = _strip_bare_decls(text)
    text = _rewrite_extends_line(text, module)
    text = _rename_header(text, bench_module_name)
    return _sm_tidy(text)


def _strip_bare_decls(text):
    return _BARE_DECL.sub("", text)


def compute_sibling_deps(targets):
    """Map output-subdir -> set of local module names that a SIBLING source file
    EXTENDS or INSTANCEs. Such a module must stay FULL (a stripped shared model
    can't serve as an EXTENDS/INSTANCE target — e.g. BPConProof INSTANCEs
    VoteProof, so VoteProof must keep all 55 ops, not its 17-op spec model)."""
    by_subdir = {}
    for path, subdir in targets:
        key = subdir if subdir is not None else os.path.splitext(os.path.basename(path))[0]
        by_subdir.setdefault(key, []).append(path)
    result = {}
    for key, paths in by_subdir.items():
        stems = {os.path.splitext(os.path.basename(p))[0] for p in paths}
        deps = set()
        for p in paths:
            try:
                with open(p, encoding="utf-8") as _f:
                    content = _f.read()
            except OSError:
                continue
            self_stem = os.path.splitext(os.path.basename(p))[0]
            for ext in parse_extends(content):
                if ext in stems and ext != self_stem:
                    deps.add(ext)
            for _, inst_mod in parse_instances(content):
                if inst_mod in stems and inst_mod != self_stem:
                    deps.add(inst_mod)
        result[key] = deps
    return result


def process_file(
    source_path,
    audit_writer,
    output_root,
    module_subdir=None,
    generated_paths=None,
    shared_model=False,
    skip_model_modules=(),
    allow_no_proof=False,
):
    """Generate L2 benchmarks for one source .tla file. Returns count emitted.

    If `generated_paths` is a list, each generated target benchmark path is
    appended to it (for downstream cross-directory dedup).
    """
    with open(source_path, encoding="utf-8") as f:
        text = f.read()
    source_lines = text.splitlines(keepends=True)

    try:
        dump = dump_sany(source_path)
    except RuntimeError as e:
        audit_writer.write(f"[level2-audit] {source_path}: SANY parse failed — {e}\n")
        return 0

    module = dump["module"]
    spec_formulas = set(dump["spec_formulas"])

    if not spec_formulas:
        audit_writer.write(f"[level2-audit] {source_path}: no spec formula identified — shape rule will not match\n")
    elif len(spec_formulas) > 1:
        audit_writer.write(f"[level2-audit] {source_path}: multiple spec formulas: {sorted(spec_formulas)}\n")
    elif "Spec" not in spec_formulas:
        only = next(iter(spec_formulas))
        audit_writer.write(f"[level2-audit] {source_path}: identified spec formula `{only}` — name != `Spec`\n")

    for t in dump["theorems"]:
        t["_keyword"] = determine_keyword(source_lines, t["loc"]["line_start"])

    theorem_candidates = [t for t in dump["theorems"] if t["_keyword"] == "THEOREM"]
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
        line = target_thm["loc"]["line_start"]
        name = target_thm["name"] or f"<unnamed L{line}>"
        has_proof = _has_manual_proof(target_thm, source_lines)
        if not has_proof and not allow_no_proof:
            audit_writer.write(
                f"[level2-audit] {source_path}: top-level THEOREM {name} at line "
                f"{line} has no manual TLAPS proof body — skipped (filter A)\n"
            )
        elif (
            os.path.splitext(os.path.basename(source_path))[0],
            target_theorem_name(target_thm)[0],
        ) in KNOWN_FALSE_TARGETS:
            # Filter A' — drop ONLY a goal TLC has shown to be false. An OMITTED
            # sub-step that papers over a *false* claim (e.g. PaxosProof
            # StructOK3) admits no honest proof, so it must not become a
            # benchmark. See KNOWN_FALSE_TARGETS for the per-target evidence.
            reason = KNOWN_FALSE_TARGETS[
                (os.path.splitext(os.path.basename(source_path))[0], target_theorem_name(target_thm)[0])
            ]
            audit_writer.write(
                f"[level2-audit] {source_path}: top-level THEOREM {name} at line "
                f"{line} asserts a FALSE goal — skipped (filter A', known-false): "
                f"{reason}\n"
            )
        elif _proof_has_omitted_substep(target_thm, source_lines):
            # An OMITTED sub-step is NO LONGER grounds for dropping: the proof is
            # structured (an OMITTED leaf still "counts as a proof"), the goal is
            # a published/verified result, and L2 grades by tlapm — not by the
            # human reference — so a missing reference proof is fine. Keep it as
            # a (hard) from-scratch benchmark. Record that it carries an OMITTED
            # sub-step for traceability.
            audit_writer.write(
                f"[level2-audit] {source_path}: top-level THEOREM {name} at line "
                f"{line} has an OMITTED sub-step — kept (goal vetted true; hard "
                f"from-scratch benchmark)\n"
            )
            survivors.append(entry)
        elif not has_proof:
            # --allow-no-proof: the source carries only PROOF OBVIOUS/OMITTED
            # (no reference proof), but the goal is a vetted hard property
            # (e.g. the ZooKeeper Zab safety theorems). L2 grades by tlapm, not
            # by the human reference, so keep it as a from-scratch benchmark.
            audit_writer.write(
                f"[level2-audit] {source_path}: top-level THEOREM {name} at line "
                f"{line} has no manual proof — kept (--allow-no-proof; tlapm-graded "
                f"from-scratch benchmark)\n"
            )
            survivors.append(entry)
        else:
            survivors.append(entry)
    top_level = survivors

    # Filter B — within-file exact-text statement dedup. Keep first by line.
    seen_stmts = {}
    deduped = []
    for entry in top_level:
        target_thm = entry[0]
        stmt = _statement_text(target_thm, source_lines)
        if stmt in seen_stmts:
            line = target_thm["loc"]["line_start"]
            kept_line = seen_stmts[stmt]
            name = target_thm["name"] or f"<unnamed L{line}>"
            audit_writer.write(
                f"[level2-audit] {source_path}: top-level THEOREM {name} at line "
                f"{line} has identical statement text to candidate kept at line "
                f"{kept_line} — skipped (filter B)\n"
            )
        else:
            seen_stmts[stmt] = target_thm["loc"]["line_start"]
            deduped.append(entry)
    top_level = deduped

    if not top_level:
        audit_writer.write(f"[level2-audit] {source_path}: no top-level THEOREM identified — no benchmarks generated\n")
        return 0
    if len(top_level) > 1:
        names = []
        for t, unnamed, shp, grph in top_level:
            label = t["name"] or f"<unnamed L{t['loc']['line_start']}>"
            tag = "[unnamed]" if unnamed else f"[shape={'Y' if shp else 'N'}/graph={'Y' if grph else 'N'}]"
            names.append(label + tag)
        audit_writer.write(f"[level2-audit] {source_path}: multiple top-level THEOREMs: {names}\n")

    out_dir = os.path.join(output_root, module_subdir or module)
    os.makedirs(out_dir, exist_ok=True)

    # Shared-model mode: emit one proof-free `<module>.tla` model and have
    # spec-based tasks EXTEND it instead of inlining the spec. A module that a
    # sibling depends on stays full (self-contained tasks) so the sibling's
    # EXTENDS/INSTANCE still resolves.
    model_set, main_specs = (set(), set())
    if shared_model and module in skip_model_modules:
        audit_writer.write(
            f"[level2-audit] {source_path}: module {module} is a local dependency "
            f"of a sibling — kept full (no shared model)\n"
        )
    if shared_model and module not in skip_model_modules:
        targets = [entry[0] for entry in top_level]
        model_set, main_specs = compute_model_set(dump, targets)
        if model_set:
            model_text = build_model(source_lines, dump, model_set)
            model_path = os.path.join(out_dir, f"{module}.tla")
            with open(model_path, "w", encoding="utf-8") as f:
                f.write(model_text)
            print(f"  generated model: {os.path.relpath(model_path, PROJECT_ROOT)}")

    base_module = os.path.splitext(os.path.basename(source_path))[0]
    used_names = set()
    count = 0
    for target_thm, _, _, _ in top_level:
        if not target_thm["name"]:
            # Not a warning: unnamed THEOREMs are top-level by construction.
            # This entry just records how the filename was derived.
            line = target_thm["loc"]["line_start"]
            rhs = target_thm["shape"].get("rhs_primary_name")
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

        reachable = compute_reachable(dump, target_thm)
        # Spec-based targets EXTEND the shared model; non-spec lemmas stay
        # self-contained (the model would over-expose context they hide).
        is_spec = target_thm["shape"].get("lhs_spec_ref") in main_specs
        if shared_model and model_set and is_spec:
            bench_text = build_benchmark_extends(
                source_lines, dump, target_thm, bench_module_name, reachable, model_set, module
            )
        else:
            bench_text = build_benchmark(source_lines, dump, target_thm, bench_module_name, reachable)
        with open(bench_file, "w", encoding="utf-8") as f:
            f.write(bench_text)
        copy_deps(dump, source_path, out_dir, reachable)
        count += 1
        if generated_paths is not None:
            generated_paths.append(bench_file)
        print(f"  generated: {os.path.relpath(bench_file, PROJECT_ROOT)}")

    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-dir", default=SOURCE_ROOT, help="Directory of source .tla files (default: %(default)s)"
    )
    parser.add_argument(
        "--output-dir", default=BENCHMARK_DIR, help="Output directory for benchmarks (default: %(default)s)"
    )
    parser.add_argument("--filter", default=None, help="Glob-ish substring to limit which source files we process")
    parser.add_argument("files", nargs="*", help="Specific .tla files to process (overrides --source-dir scan)")
    parser.add_argument(
        "--shared-model",
        action="store_true",
        help="Emit one proof-free <Module>.tla model per output dir "
        "and have spec-based tasks EXTEND it instead of inlining "
        "the spec (de-duplicates the spec; grader resolves the "
        "co-located model automatically).",
    )
    parser.add_argument(
        "--allow-no-proof",
        action="store_true",
        help="Keep top-level theorems whose source has only PROOF "
        "OBVIOUS/OMITTED (no reference proof). Use for vetted "
        "hard from-scratch benchmarks (e.g. ZooKeeper Zab) that "
        "are graded by tlapm, not against a human reference.",
    )
    args = parser.parse_args()

    output_root = os.path.abspath(args.output_dir)
    os.makedirs(output_root, exist_ok=True)
    audit_path = os.path.join(output_root, "audit.log")

    if args.files:
        targets = [(os.path.abspath(p), None) for p in args.files]
    else:
        src_root = os.path.abspath(args.source_dir)
        targets = []
        for root, _, files in os.walk(src_root):
            if ".tlaps" in root:
                continue
            for fname in sorted(files):
                if not fname.endswith(".tla"):
                    continue
                full = os.path.join(root, fname)
                if args.filter and args.filter not in full:
                    continue
                subdir = os.path.relpath(root, src_root).split(os.sep)[0]
                if subdir == ".":
                    subdir = os.path.splitext(fname)[0]
                targets.append((full, subdir))

    sibling_deps = compute_sibling_deps(targets) if args.shared_model else {}

    total = 0
    generated_paths = []
    with open(audit_path, "w", encoding="utf-8") as audit_writer:
        for path, subdir in targets:
            print(f"\nProcessing {os.path.relpath(path, PROJECT_ROOT)}")
            key = subdir if subdir is not None else os.path.splitext(os.path.basename(path))[0]
            try:
                total += process_file(
                    path,
                    audit_writer,
                    output_root,
                    module_subdir=subdir,
                    generated_paths=generated_paths,
                    shared_model=args.shared_model,
                    skip_model_modules=sibling_deps.get(key, set()),
                    allow_no_proof=args.allow_no_proof,
                )
            except Exception as e:
                audit_writer.write(f"[level2-audit] {path}: ERROR {e!r}\n")
                print(f"  ERROR: {e}", file=sys.stderr)
        removed = cross_dir_dedup(generated_paths, audit_writer)

    print(f"\nTotal L2 benchmarks: {total - removed} ({total} generated, {removed} removed by cross-dir dedup)")
    print(f"Audit log: {os.path.relpath(audit_path, PROJECT_ROOT)}")


if __name__ == "__main__":
    main()
