"""proof-from-scratch layered emission — the generator side of the Issue #64 boundary.

The generator and the evaluator implement two halves of one contract: the
generator emits read-only context, an editable task carrying the four marker
lines, and a manifest naming each task's exact context; the evaluator
(``src/common/proof_from_scratch_contract.py``) parses exactly that. These tests
pin the generator-side invariants that contract depends on, without needing
SANY or tlapm.

Run: PYTHONPATH=src python3 -m pytest tests/dataset/test_layered_generator.py
"""

import json
import pathlib

import pytest

from dataset.proof_from_scratch import generate
from dataset.proof_from_scratch.generate import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
    _defined_names,
    _strip_module_directives,
    _unneeded_decl_edits,
    build_task_module,
    copy_deps_layered,
    dep_keep_names,
    layered_cross_dir_dedup,
    prune_dep_module,
    referenced_identifiers,
    stage_benchmark_only_sources,
)


def test_task_module_has_markers_once_and_in_order():
    text = build_task_module("Foo_Thm", "Foo_ThmDefs", "THEOREM Spec => []Inv")
    for marker in (BEGIN_AGENT_HELPERS, END_AGENT_HELPERS, BEGIN_AGENT_PROOF, END_AGENT_PROOF):
        assert text.count(marker) == 1, f"{marker} must appear exactly once"
    order = [text.index(m) for m in (BEGIN_AGENT_HELPERS, END_AGENT_HELPERS, BEGIN_AGENT_PROOF, END_AGENT_PROOF)]
    assert order == sorted(order)
    # Markers must be their own lines: the evaluator matches whole lines.
    lines = text.splitlines()
    for marker in (BEGIN_AGENT_HELPERS, END_AGENT_HELPERS, BEGIN_AGENT_PROOF, END_AGENT_PROOF):
        assert marker in lines


def test_task_module_ships_an_empty_helper_region_and_placeholder_proof():
    text = build_task_module("Foo_Thm", "Foo_ThmDefs", "THEOREM Spec => []Inv")
    helpers = text.split(BEGIN_AGENT_HELPERS)[1].split(END_AGENT_HELPERS)[0]
    proof = text.split(BEGIN_AGENT_PROOF)[1].split(END_AGENT_PROOF)[0]
    assert helpers.strip() == ""
    assert proof.strip() == "PROOF OBVIOUS"


def test_task_module_imports_only_its_defs_layer():
    text = build_task_module("Foo_Thm", "Foo_ThmDefs", "THEOREM TRUE")
    assert "EXTENDS Foo_ThmDefs" in text
    assert text.startswith("---- MODULE Foo_Thm ----")
    # The theorem is fixed scaffold, never inside an editable region.
    assert text.index("THEOREM TRUE") > text.index(END_AGENT_HELPERS)
    assert text.index("THEOREM TRUE") < text.index(BEGIN_AGENT_PROOF)


def test_module_directives_are_stripped_from_read_only_layers():
    # `USE`/`HIDE` are prover hints from the original proof; leaving them in a
    # read-only layer would hand the agent part of the proof strategy.
    text = "Op == 1\nUSE DEF Op\n  HIDE DEF Op\nOther == 2\n"
    assert _strip_module_directives(text) == "Op == 1\nOther == 2\n"


def test_quantifier_is_not_read_as_a_use_of_a_variable_named_a():
    """`\\A x \\in S` must not count as a use of a VARIABLE named `A`.

    Regression: BubbleSort declares `VARIABLES A, A0, ...` after a theorem that
    binds `\\A A, B, C`. Hoisting that declaration into a module the task
    EXTENDS makes it shadow the bound variable and SANY rejects the task, so an
    unused declaration must actually be dropped.
    """
    source = "Perms == { f \\in S : \\A p \\in 1..N : TRUE }\n\nVARIABLES A, A0\n"
    dump = {
        "operators": [{"name": "Perms", "loc": {"line_start": 1, "line_end": 1}}],
        "assumes": [],
        "constants": [],
        "variables": [
            {"name": "A", "loc": {"line_start": 3, "line_end": 3}},
            {"name": "A0", "loc": {"line_start": 3, "line_end": 3}},
        ],
    }
    edits = _unneeded_decl_edits(source.splitlines(keepends=True), dump, {"Perms"})
    assert edits == [(3, 3, "")], "VARIABLE A is unused and must be dropped"


def test_declaration_actually_referenced_is_kept():
    source = "Init == x = 0\n\nVARIABLE x\n"
    dump = {
        "operators": [{"name": "Init", "loc": {"line_start": 1, "line_end": 1}}],
        "assumes": [],
        "constants": [],
        "variables": [{"name": "x", "loc": {"line_start": 3, "line_end": 3}}],
    }
    assert _unneeded_decl_edits(source.splitlines(keepends=True), dump, {"Init"}) == []


def _write_task(root, subdir, name, body="THEOREM TRUE", defs_body="Inv == TRUE"):
    d = root / subdir
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{name}.tla").write_text(build_task_module(name, f"{name}Defs", body))
    (d / f"{name}Defs.tla").write_text(f"---- MODULE {name}Defs ----\n{defs_body}\n====\n")
    return f"{subdir}/{name}.tla", {"context": [f"{subdir}/{name}Defs.tla"]}


def test_cross_dir_dedup_keeps_the_preferred_copy_and_sweeps_its_context(tmp_path, capsys):
    manifest = {}
    for subdir in ("Consensus", "Data"):
        key, entry = _write_task(tmp_path, subdir, "Sets_Thm")
        manifest[key] = entry
    # A task that differs only in its context must NOT be deduped.
    key, entry = _write_task(tmp_path, "Other", "Sets_Thm", defs_body="Inv == FALSE")
    manifest[key] = entry

    class _Audit:
        def write(self, _):
            pass

    removed = layered_cross_dir_dedup(str(tmp_path), manifest, _Audit())

    assert removed == 1
    assert "Data/Sets_Thm.tla" in manifest, "the Data/ copy is preferred"
    assert "Consensus/Sets_Thm.tla" not in manifest
    assert "Other/Sets_Thm.tla" in manifest, "different context is a different task"
    # The losing task's files are gone; survivors' context is untouched.
    assert not (tmp_path / "Consensus" / "Sets_Thm.tla").exists()
    assert not (tmp_path / "Consensus" / "Sets_ThmDefs.tla").exists()
    assert (tmp_path / "Data" / "Sets_ThmDefs.tla").exists()
    assert (tmp_path / "Other" / "Sets_ThmDefs.tla").exists()


def test_manifest_round_trips_as_json(tmp_path):
    manifest = {}
    key, entry = _write_task(tmp_path, "Peterson", "Peterson_MutualExclusion")
    manifest[key] = entry
    text = json.dumps(dict(sorted(manifest.items())), indent=2)
    assert json.loads(text) == manifest


def test_multi_line_declaration_statement_is_deleted_as_one_unit():
    """A `VARIABLE a,\\n b` statement must never be half-deleted.

    Regression: SANY reports a separate loc per declared name, so deleting only
    the unused name's line left a dangling `VARIABLE votes,` that SANY rejects
    (tlaplus_examples_Paxos/Voting.tla declares `votes` and `maxBal` this way).
    """
    source = "VARIABLE votes,   \\* comment\n         maxBal\nOp == 1\n"
    lines = source.splitlines(keepends=True)
    dump = {
        "operators": [{"name": "Op", "loc": {"line_start": 3, "line_end": 3}}],
        "assumes": [],
        "constants": [],
        "variables": [
            {"name": "votes", "loc": {"line_start": 1, "line_end": 1}},
            {"name": "maxBal", "loc": {"line_start": 2, "line_end": 2}},
        ],
    }
    # Neither name is used by the kept definition, so the whole statement goes.
    assert _unneeded_decl_edits(lines, dump, {"Op"}) == [(1, 2, "")]


def test_partially_used_declaration_statement_is_kept_whole():
    source = "VARIABLE votes,\n         maxBal\nOp == votes\n"
    lines = source.splitlines(keepends=True)
    dump = {
        "operators": [{"name": "Op", "loc": {"line_start": 3, "line_end": 3}}],
        "assumes": [],
        "constants": [],
        "variables": [
            {"name": "votes", "loc": {"line_start": 1, "line_end": 1}},
            {"name": "maxBal", "loc": {"line_start": 2, "line_end": 2}},
        ],
    }
    # `maxBal` is unused but shares the statement with the used `votes`.
    assert _unneeded_decl_edits(lines, dump, {"Op"}) == []


def test_surviving_instance_disables_declaration_pruning():
    """An INSTANCE substitutes declarations implicitly, so nothing may be pruned.

    Regression: LockHS declares `VARIABLE s` purely to satisfy
    `INSTANCE Stuttering`, which substitutes it by name without mentioning it.
    Pruning it produced "Substitution missing for symbol s" under SANY.
    """
    source = "VARIABLE s\nINSTANCE Stuttering\nOp == 1\n"
    lines = source.splitlines(keepends=True)
    dump = {
        "operators": [{"name": "Op", "loc": {"line_start": 3, "line_end": 3}}],
        "assumes": [],
        "constants": [],
        "variables": [{"name": "s", "loc": {"line_start": 1, "line_end": 1}}],
        # An unnamed INSTANCE is always kept, so pruning must be skipped.
        "instances": [{"name": None, "module": "Stuttering", "loc": {"line_start": 2, "line_end": 2}}],
    }
    assert _unneeded_decl_edits(lines, dump, {"Op"}) == []


def test_copied_dependency_keeps_no_theorem_to_cite(tmp_path, monkeypatch):
    """A context module must not ship a THEOREM the agent can cite.

    Regression: `copy_deps` rewrote a dependency's proofs to `PROOF OMITTED` and
    kept the statements. An OMITTED theorem is a usable fact, so
    `Voting_proof_AllSafeAtZero_T` — whose goal restates `AllSafeAtZero` — was
    discharged by `BY AllSafeAtZero` without proving anything.
    """
    src = tmp_path / "src"
    src.mkdir()
    (src / "Dep.tla").write_text(
        "---- MODULE Dep ----\n"
        "SafeAt(b, v) == TRUE\n"
        "THEOREM AllSafeAtZero == \\A v \\in Value : SafeAt(0, v)\n"
        "<1>1. TRUE OBVIOUS\n"
        "<1> QED BY <1>1\n"
        "====\n"
    )
    (src / "Main.tla").write_text("---- MODULE Main ----\nEXTENDS Dep\n====\n")
    out = tmp_path / "out"
    out.mkdir()

    dump = {"extends": ["Dep"], "instances": []}
    copied = copy_deps_layered(dump, str(src / "Main.tla"), str(out), set())

    assert copied == ["Dep.tla"]
    text = (out / "Dep.tla").read_text()
    assert "SafeAt" in text, "given definitions must survive"
    assert "THEOREM" not in text, "no goal may remain for the agent to cite"
    assert "AllSafeAtZero" not in text
    assert "OMITTED" not in text


def test_defined_names_reads_back_emitted_definitions():
    text = "---- MODULE M ----\nInv == TRUE\nSafeAt(b, v) == TRUE\nTHEOREM T == TRUE\n====\n"
    assert _defined_names(text) == {"Inv", "SafeAt"}


def test_prune_dep_module_drops_proof_helpers_but_keeps_needed_definitions(tmp_path, monkeypatch):
    """A dependency must not hand over the original proof's scaffolding.

    `TypeOK` is an inductive invariant no task's statement mentions, so it is
    exactly what a from-scratch task should make the agent rediscover;
    `Coherence` is named by the target theorem and has to stay.
    """
    dep = tmp_path / "Dep.tla"
    dep.write_text(
        "---- MODULE Dep ----\nVARIABLE x\nCoherence == x = 1\nTypeOK == x \\in Nat\nTHEOREM Safety == TypeOK\n====\n"
    )
    fake_dump = {
        "operators": [
            {"name": "Coherence", "loc": {"line_start": 3, "line_end": 3}, "references": []},
            {"name": "TypeOK", "loc": {"line_start": 4, "line_end": 4}, "references": []},
        ],
        "instances": [],
        "assumes": [],
    }
    monkeypatch.setattr(generate, "dump_sany", lambda _p: fake_dump)

    text = prune_dep_module(str(dep), {"Coherence"})

    assert "Coherence" in text, "a definition the target statement needs must stay"
    assert "TypeOK" not in text, "an unused proof helper must be pruned"
    assert "THEOREM" not in text, "a dependency never states a goal"
    assert "VARIABLE x" in text, "declarations are always kept"


def test_dep_keep_names_returns_none_when_an_unnamed_instance_is_present(tmp_path, monkeypatch):
    """An unnamed INSTANCE re-exports names implicitly, so nothing is provably
    unused and the whole group must be kept."""
    dep = tmp_path / "Dep.tla"
    dep.write_text("---- MODULE Dep ----\nINSTANCE Other\nTypeOK == TRUE\n====\n")
    fake_dump = {
        "operators": [{"name": "TypeOK", "loc": {"line_start": 3, "line_end": 3}, "references": []}],
        "instances": [{"name": None, "module": "Other", "loc": {"line_start": 2, "line_end": 2}}],
        "assumes": [],
    }
    monkeypatch.setattr(generate, "dump_sany", lambda _p: fake_dump)

    assert dep_keep_names([str(dep)], set()) is None
    # keep_names=None means "keep every definition".
    assert "TypeOK" in prune_dep_module(str(dep), None)


def test_dep_keep_names_closes_across_sibling_dependencies(tmp_path, monkeypatch):
    """Closure must span the group: a definition one dep needs from another
    must survive, or the pruned module stops parsing."""
    a, b = tmp_path / "A.tla", tmp_path / "B.tla"
    a.write_text("---- MODULE A ----\nUsesChosen == chosen\n====\n")
    b.write_text("---- MODULE B ----\nchosen == 1\nUnused == 2\n====\n")
    dumps = {
        str(a): {
            "operators": [{"name": "UsesChosen", "loc": {"line_start": 2, "line_end": 2}, "references": ["chosen"]}],
            "instances": [],
            "assumes": [],
        },
        str(b): {
            "operators": [
                {"name": "chosen", "loc": {"line_start": 2, "line_end": 2}, "references": []},
                {"name": "Unused", "loc": {"line_start": 3, "line_end": 3}, "references": []},
            ],
            "instances": [],
            "assumes": [],
        },
    }
    monkeypatch.setattr(generate, "dump_sany", lambda p: dumps[str(p)])

    keep = dep_keep_names([str(a), str(b)], {"UsesChosen"})

    assert "chosen" in keep, "a sibling dep's definition must survive"
    assert "Unused" not in keep


def test_referenced_identifiers_ignores_tla_backslash_operators():
    assert "A" not in referenced_identifiers("\\A p \\in S : TRUE")
    assert {"p", "S", "TRUE"} <= referenced_identifiers("\\A p \\in S : TRUE")


def test_missing_tlapm_fails_generation_rather_than_skipping(tmp_path, monkeypatch):
    """A degenerate task PASSes with an empty submission, so it must never ship.

    Without tlapm the gate cannot tell, and skipping would let one through, so
    generation fails instead. `--skip-gates` is the deliberate opt-out.
    """
    monkeypatch.setattr(generate, "find_tlapm", lambda: None, raising=False)
    monkeypatch.setattr("dataset.triviality_audit.find_tlapm", lambda: None)

    class _Audit:
        def write(self, _):
            pass

    with pytest.raises(RuntimeError, match="tlapm not found"):
        generate.layered_triviality_gate(str(tmp_path), {}, _Audit())


def test_stage_benchmark_only_sources_picks_up_dirs_missing_from_source(tmp_path):
    """OpenAddressing and etcd_raft live only under the benchmark tree; scanning
    `source/` alone silently loses those tasks."""
    src = tmp_path / "source"
    (src / "Peterson").mkdir(parents=True)
    legacy = tmp_path / "benchmark"
    (legacy / "Peterson").mkdir(parents=True)  # mirrored — must be skipped
    (legacy / "etcd_raft").mkdir(parents=True)
    (legacy / "etcd_raft" / "EtcdRaft.tla").write_text("---- MODULE EtcdRaft ----\n====\n")
    (legacy / "etcd_raft" / "etcd_raft_LogInv.tla").write_text(
        "---- MODULE etcd_raft_LogInv ----\nTHEOREM Spec => []LogInv\n====\n"
    )

    targets = stage_benchmark_only_sources(str(src), str(legacy))

    subdirs = {sub for _p, sub in targets}
    assert subdirs == {"etcd_raft"}, "only directories absent from source/ are staged"
    # Only the task file is a target; EtcdRaft.tla is a dependency, and treating
    # a theorem library as a source would turn each of its lemmas into a task.
    assert [pathlib.Path(p).name for p, _ in targets] == ["etcd_raft_LogInv.tla"]
    # Staged out of the benchmark tree, which is also the output tree.
    assert all(str(legacy) not in path for path, _ in targets)


def test_stage_benchmark_only_sources_disabled_when_no_legacy_root():
    assert stage_benchmark_only_sources("/nonexistent/source", "") == []


def test_subscript_names_are_seen_as_references():
    """`[][Next]_vars` and `WF_vars(p)` bind `vars` with a leading underscore.

    Regression: the raw token is `_vars`, so `vars` looked unused and was pruned
    out of a dependency that still needed it (Unknown operator: `vars').
    """
    names = referenced_identifiers("Spec == Init /\\ [][Next]_vars /\\ WF_vars(proc)")
    assert "vars" in names
    assert {"Init", "Next", "Spec", "proc"} <= names
