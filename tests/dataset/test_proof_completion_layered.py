"""proof-completion layered emission — the generator side of the Issue #86 boundary.

The generator and the evaluator implement two halves of one contract: the
generator emits read-only model + scaffold layers, an editable task carrying the
proof markers, and a manifest naming each task's exact context; the evaluator
(``src/common/proof_completion_contract.py``) parses exactly that. These tests
pin the generator-side invariants that contract depends on, without needing SANY
or tlapm.

Run: PYTHONPATH=src python3 -m pytest tests/dataset/test_proof_completion_layered.py
"""

import json
import os
from io import StringIO
from pathlib import Path

import pytest

from common.proof_completion_contract import (
    BEGIN_AGENT_PROOF,
    END_AGENT_PROOF,
    ManifestError,
    load_proof_completion_manifest,
    parse_proof_completion_region,
)
from common.task_contract import BEGIN_AGENT_HELPERS, END_AGENT_HELPERS
from dataset.proof_completion.generate import (
    _engine,
    _finalize_layered,
    _promote_dataset,
    _seed_staging,
    build_prefix_model,
    build_scaffold,
    build_task_module,
    dependency_module_text,
    drop_known_degenerate,
    layered_duplicate_gate,
    load_dataset_task_keys,
    module_directives_before,
    strip_proof_step_comments,
    target_statement_text,
    write_task_dependencies,
)

SOURCE = """---- MODULE Src ----
EXTENDS Naturals, TLAPS
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = x + 1
Spec == Init /\\ [][Next]_x
Inv == x \\in Nat
USE DEF Inv
LEMMA Base == Inv
<1>1. TRUE
<1> QED
LEMMA Target == Spec => []Inv
<1>1. TRUE
<1> QED
THEOREM Later == TRUE
PROOF OBVIOUS
====
"""


def _dump():
    """A hand-written SANY dump for SOURCE — the tests never invoke SANY."""

    def thm(name, start, end, proof_start, proof_end, column=1):
        return {
            "name": name,
            "loc": {"line_start": start, "line_end": end},
            "proof_loc": {"line_start": proof_start, "line_end": proof_end, "column_start": column},
        }

    def op(name, line):
        return {"name": name, "loc": {"line_start": line, "line_end": line}}

    return {
        "module": "Src",
        "theorems": [thm("Base", 10, 12, 11, 12), thm("Target", 13, 15, 14, 15), thm("Later", 16, 17, 17, 17)],
        "operators": [op("Init", 5), op("Next", 6), op("Spec", 7), op("Inv", 8)],
        "instances": [],
        "constants": [{"name": "N", "loc": {"line_start": 3, "line_end": 3}}],
        "variables": [{"name": "x", "loc": {"line_start": 4, "line_end": 4}}],
        "assumes": [],
        "extends": ["Naturals", "TLAPS"],
        "spec_formulas": ["Spec"],
    }


def _lines():
    return SOURCE.splitlines(keepends=True)


def _target():
    return _dump()["theorems"][1]


def test_custom_source_dir_is_used_for_specification_identity(tmp_path, monkeypatch):
    import dataset.proof_completion.generate as generate

    source_root = tmp_path / "custom-source"
    source = source_root / "Group" / "Spec.tla"
    source.parent.mkdir(parents=True)
    source.write_text("---- MODULE Spec ----\n====\n")
    observed_roots = []

    def fake_emit(_sm, _path, _subdir, _out_dir, _audit, _manifest, _state, _reference, *, source_root):
        observed_roots.append(source_root)
        return 0

    monkeypatch.setattr(generate, "emit_layered_source", fake_emit)
    monkeypatch.setattr(generate, "_finalize_layered", lambda *_args, **_kwargs: 0)

    generate.generate_layered(
        output_root=str(tmp_path / "benchmark"),
        source_dir=str(source_root),
        run_gates=False,
    )

    assert observed_roots == [str(source_root)]


# --- the editable task file ------------------------------------------------


def test_task_module_has_proof_markers_once_and_in_order():
    text = build_task_module("Src_Target", "Src_TargetScaffold", "LEMMA Target == Spec => []Inv")
    for marker in (BEGIN_AGENT_PROOF, END_AGENT_PROOF):
        assert text.count(marker) == 1, f"{marker} must appear exactly once"
    assert text.index(BEGIN_AGENT_PROOF) < text.index(END_AGENT_PROOF)
    # Markers must be their own lines: the evaluator matches whole lines.
    lines = text.splitlines()
    assert BEGIN_AGENT_PROOF in lines and END_AGENT_PROOF in lines


def test_task_module_has_no_helper_region():
    """proof completion gives the scaffolding; the agent adds no module-level helpers."""
    text = build_task_module("Src_Target", "Src_TargetScaffold", "LEMMA Target == TRUE")
    assert BEGIN_AGENT_HELPERS not in text
    assert END_AGENT_HELPERS not in text


def test_task_module_parses_under_the_evaluator_contract():
    text = build_task_module("Src_Target", "Src_TargetScaffold", "LEMMA Target == TRUE")
    regions = parse_proof_completion_region(text)
    assert regions.proof.strip() == "PROOF OBVIOUS"
    # The theorem statement is fixed scaffold, never inside the editable region.
    assert "LEMMA Target == TRUE" in regions.fixed_prefix
    assert regions.render(proof="PROOF BY Base\n") != text


def test_task_module_imports_only_its_scaffold_layer():
    text = build_task_module("Src_Target", "Src_TargetScaffold", "LEMMA Target == TRUE")
    assert text.startswith("---- MODULE Src_Target ----\nEXTENDS Src_TargetScaffold\n")


def test_module_directives_travel_with_the_theorem():
    """`USE` is not inherited through EXTENDS, so it must reach the task file.

    Leaving `USE DEF Inv` behind in the scaffold silently drops a fact the
    reference proof relies on — the scaffold proves nothing, so it has no effect
    there. It lands outside the proof region, so it stays benchmark-owned.
    """
    text = build_task_module("Src_Target", "Src_TargetScaffold", "LEMMA Target == TRUE", ["USE DEF Inv"])
    regions = parse_proof_completion_region(text)
    assert "USE DEF Inv" in regions.fixed_prefix
    assert "USE DEF Inv" not in regions.proof
    assert text.index("USE DEF Inv") < text.index("LEMMA Target == TRUE")


def test_module_directives_before_skips_proof_local_and_later_directives():
    lines = [
        "---- MODULE Src ----\n",
        "USE DEF Early\n",
        "LEMMA A == TRUE\n",
        "  USE DEF InsideProof\n",
        "USE DEF AlsoInsideProof\n",
        "LEMMA Target == TRUE\n",
        "USE DEF After\n",
    ]
    dump = {"theorems": [{"loc": {"line_start": 3, "line_end": 5}, "proof_loc": {"line_start": 4, "line_end": 5}}]}
    assert module_directives_before(lines, dump, target_line=6) == ["USE DEF Early"]


# --- the fixed theorem statement -------------------------------------------


def test_statement_text_stops_where_the_proof_starts():
    sm = _engine()
    assert target_statement_text(sm, _lines(), _target()) == "LEMMA Target == Spec => []Inv"


def test_statement_text_splits_a_one_line_lemma_at_the_proof_column():
    """`LEMMA Foo == x  BY DEF y` puts statement and proof on one line."""
    sm = _engine()
    lines = ["LEMMA Foo == TRUE  BY DEF Bar\n"]
    thm = {
        "name": "Foo",
        "loc": {"line_start": 1, "line_end": 1},
        "proof_loc": {"line_start": 1, "line_end": 1, "column_start": 20},
    }
    assert target_statement_text(sm, lines, thm) == "LEMMA Foo == TRUE"


def test_statement_text_drops_comments_that_carry_the_original_proof_sketch():
    sm = _engine()
    lines = [
        "LEMMA Foo ==\n",
        "  (* proved by induction, see <1>2 below *)\n",
        "  TRUE\n",
        "OBVIOUS\n",
    ]
    thm = {
        "name": "Foo",
        "loc": {"line_start": 1, "line_end": 4},
        "proof_loc": {"line_start": 4, "line_end": 4, "column_start": 1},
    }
    statement = target_statement_text(sm, lines, thm)
    assert "<1>2" not in statement
    assert statement.splitlines()[0] == "LEMMA Foo =="
    assert statement.rstrip().endswith("TRUE")


# --- the read-only scaffold layer ------------------------------------------


def _scaffold(model_set=frozenset({"Init", "Next", "Spec"})):
    return build_scaffold(_engine(), _lines(), _dump(), _target(), "Src_TargetScaffold", "SrcModel", set(model_set))


def test_scaffold_keeps_given_definitions_and_admits_preceding_proofs():
    text = _scaffold()
    assert "Inv == x \\in Nat" in text, "proof completion gives the agent the invariant"
    assert "LEMMA Base == Inv" in text
    assert "PROOF OMITTED" in text
    assert "<1>1." not in text, "a preceding reference proof must not survive"


def test_scaffold_removes_the_target_and_every_later_theorem():
    body = _scaffold().split("\n", 1)[1]  # past the `MODULE Src_TargetScaffold` header
    assert "Target" not in body, "the target theorem belongs to the task file"
    assert "Later" not in body, "a theorem stated after the target is not a given"


def test_scaffold_inherits_declarations_and_spec_from_the_model():
    text = _scaffold()
    assert text.startswith("---- MODULE Src_TargetScaffold ----")
    assert "EXTENDS SrcModel" in text
    for owned_by_the_model in ("CONSTANT N", "VARIABLE x", "Init ==", "Next ==", "Spec =="):
        assert owned_by_the_model not in text, f"{owned_by_the_model} is the model's, not the scaffold's"


def test_scaffold_without_a_model_stays_self_contained():
    text = _scaffold(model_set=frozenset())
    assert "EXTENDS Naturals, TLAPS" in text
    assert "CONSTANT N" in text
    assert "Spec ==" in text


def test_scaffold_stops_at_the_target_so_a_later_declaration_cannot_shadow_it():
    """Regression: BubbleSort binds `\\A A \\in ...` before `VARIABLES A, A0`.

    In one flat file that is legal — the declaration comes later, so it does not
    shadow the bound name. Hoisted into a module the task EXTENDS it always is
    in scope, and SANY rejects the task with a multiply-defined symbol.
    """
    source = (
        "---- MODULE Src ----\n"
        "EXTENDS Integers\n"
        "CONSTANT N\n"
        "THEOREM Bind == \\A A \\in 1..N : A = A\n"
        "OBVIOUS\n"
        "VARIABLES A, A0\n"
        "Init == A = 0\n"
        "====\n"
    )
    dump = {
        "theorems": [
            {
                "name": "Bind",
                "loc": {"line_start": 4, "line_end": 5},
                "proof_loc": {"line_start": 5, "line_end": 5, "column_start": 1},
            }
        ],
        "operators": [{"name": "Init", "loc": {"line_start": 7, "line_end": 7}}],
        "instances": [],
        "constants": [{"name": "N", "loc": {"line_start": 3, "line_end": 3}}],
        "variables": [
            {"name": "A", "loc": {"line_start": 6, "line_end": 6}},
            {"name": "A0", "loc": {"line_start": 6, "line_end": 6}},
        ],
        "assumes": [],
    }
    text = build_scaffold(
        _engine(), source.splitlines(keepends=True), dump, dump["theorems"][0], "Src_BindScaffold", None, set()
    )
    assert "CONSTANT N" in text, "what precedes the target is still a given"
    assert "VARIABLES A, A0" not in text
    assert "Init ==" not in text
    assert text.rstrip().endswith("="), "truncation must leave a module terminator"


def test_scaffold_drops_module_directives():
    # `USE`/`HIDE` are dead in a scaffold (it proves nothing) and belong with the
    # theorem; leaving a copy behind would only mislead.
    assert "USE DEF Inv" not in _scaffold()


def test_proof_step_comments_are_dropped_but_prose_is_kept():
    text = "(* A prose note. *)\nOp == 1\n(* see step <1>2 for the trick *)\n\\* <2>3 leftover\n\\* keep me\n"
    cleaned = strip_proof_step_comments(text)
    assert "A prose note" in cleaned
    assert "keep me" in cleaned
    assert "<1>2" not in cleaned
    assert "<2>3" not in cleaned
    assert cleaned.count("\n") == text.count("\n"), "line geometry must survive"


# --- the read-only model layer ---------------------------------------------

MODEL_SET = frozenset({"Init", "Next", "Spec"})


def test_model_holds_the_state_machine_the_scaffold_gives_up():
    text = build_prefix_model(_engine(), _lines(), _dump(), set(MODEL_SET), target_start=13)
    for owned_by_the_model in ("CONSTANT N", "VARIABLE x", "Init ==", "Next ==", "Spec =="):
        assert owned_by_the_model in text
    assert "Inv ==" not in text, "the invariant is the scaffold's given, not the model's"
    assert "LEMMA Base" not in text, "a model must never carry a theorem"
    assert text.rstrip().endswith("="), "truncation must leave a module terminator"


def test_model_stops_at_the_target_so_a_later_definition_stays_out_of_scope():
    """Regression: `Voting` states `THEOREM QuorumNonEmpty` before defining `Ballot`.

    One model built from every target in the file hoists `Ballot` (and the rest
    of the state machine) ahead of a theorem the source states above it, so
    `BY QuorumAssumption DEF Ballot` closes a task that cannot name `Ballot` in
    the source. Truncating the model at the target restores the original scope.
    """
    source = (
        "---- MODULE Src ----\n"
        "EXTENDS Integers\n"
        "CONSTANT Quorum\n"
        "ASSUME QuorumAssumption == \\A Q \\in Quorum : Q # {}\n"
        "THEOREM Early == \\A Q \\in Quorum : Q # {}\n"
        "BY QuorumAssumption\n"
        "Ballot == Nat\n"
        "Spec == Ballot = Nat\n"
        "THEOREM Late == Spec\n"
        "BY DEF Spec, Ballot\n"
        "====\n"
    )
    dump = {
        "theorems": [
            {
                "name": "Early",
                "loc": {"line_start": 5, "line_end": 6},
                "proof_loc": {"line_start": 6, "line_end": 6, "column_start": 1},
            },
            {
                "name": "Late",
                "loc": {"line_start": 9, "line_end": 10},
                "proof_loc": {"line_start": 10, "line_end": 10, "column_start": 1},
            },
        ],
        "operators": [
            {"name": "Ballot", "loc": {"line_start": 7, "line_end": 7}},
            {"name": "Spec", "loc": {"line_start": 8, "line_end": 8}},
        ],
        "instances": [],
        "constants": [{"name": "Quorum", "loc": {"line_start": 3, "line_end": 3}}],
        "variables": [],
        "assumes": [{"name": "QuorumAssumption", "loc": {"line_start": 4, "line_end": 4}}],
    }
    lines = source.splitlines(keepends=True)
    model_set = {"Ballot", "Spec"}

    early = build_prefix_model(_engine(), lines, dump, model_set, target_start=5)
    assert "ASSUME QuorumAssumption" in early, "what precedes the target is still a given"
    assert "Ballot ==" not in early, "a definition stated after the target is out of its scope"
    assert "Spec ==" not in early

    late = build_prefix_model(_engine(), lines, dump, model_set, target_start=9)
    assert "Ballot ==" in late and "Spec ==" in late
    assert "THEOREM Early" not in late, "a model must never carry a theorem"


def test_targets_with_the_same_prefix_yield_one_shared_model():
    """Dedup key: identical bodies must let two targets share one model file."""
    engine = _engine()
    first = build_prefix_model(engine, _lines(), _dump(), set(MODEL_SET), target_start=13)
    second = build_prefix_model(engine, _lines(), _dump(), set(MODEL_SET), target_start=16)
    assert first == second, "nothing is defined between the two targets, so one model serves both"


# --- dependency context ----------------------------------------------------


DEP = """---- MODULE Dep ----
Helper == TRUE
(* a comment *)
LEMMA DepFact == Helper
<1>1. TRUE
<1> QED
====
"""


def test_dependency_keeps_statements_and_admits_their_proofs(tmp_path):
    path = tmp_path / "Dep.tla"
    path.write_text(DEP)
    text = dependency_module_text(_engine(), str(path))
    assert "LEMMA DepFact == Helper" in text, "a dependency lemma is a usable given"
    assert "PROOF OMITTED" in text
    assert "<1>1." not in text
    assert "a comment" not in text


def test_standalone_proof_obvious_is_read_as_a_proof_body(tmp_path):
    """`PROOF OBVIOUS` on its own line must not be left orphaned.

    A dependency whose theorem is rewritten to `PROOF OMITTED` used to keep the
    unrecognised `PROOF OBVIOUS` line as well, and SANY then rejected the whole
    module (source/OpenAddressing/OpenAddressing.tla).
    """
    path = tmp_path / "Dep.tla"
    path.write_text("---- MODULE Dep ----\nOp == 1\nTHEOREM Spec => []Op\nPROOF OBVIOUS\n====\n")
    text = dependency_module_text(_engine(), str(path))
    assert text.count("PROOF") == 1
    assert "PROOF OBVIOUS" in text


class _StubEngine:
    """The real engine, with a fixed dependency list instead of a SANY dump."""

    def __init__(self, deps):
        self._deps = deps
        self.strip_comments = _engine().strip_comments

    def layered_dep_paths(self, dump, source_path, reachable):
        return self._deps


def test_conflicting_dependency_basenames_get_a_private_copy(tmp_path):
    class _Writer:
        def __init__(self):
            self.lines = []

        def write(self, line):
            self.lines.append(line)

    first = tmp_path / "a" / "Dep.tla"
    second = tmp_path / "b" / "Dep.tla"
    first.parent.mkdir(parents=True)
    second.parent.mkdir(parents=True)
    first.write_text("---- MODULE Dep ----\nHelper == 1\n====\n")
    second.write_text("---- MODULE Dep ----\nHelper == 2\n====\n")

    out_dir = tmp_path / "out" / "Group"
    out_dir.mkdir(parents=True)
    written = {}
    writer = _Writer()

    shared = write_task_dependencies(
        _StubEngine([("Dep", str(first))]), {}, "src.tla", str(out_dir), "Group", "Group_One", writer, written
    )
    private = write_task_dependencies(
        _StubEngine([("Dep", str(second))]), {}, "src.tla", str(out_dir), "Group", "Group_Two", writer, written
    )

    assert shared == ["Group/Dep.tla"]
    assert private == ["Group/Group_Two/Dep.tla"], "the second module must not overwrite the first"
    assert (out_dir / "Group_Two" / "Dep.tla").read_text().find("Helper == 2") > 0
    assert "Helper == 1" in (out_dir / "Dep.tla").read_text()
    assert any("conflicts with another module" in line for line in writer.lines)


# --- dataset selection and the manifest ------------------------------------


def test_dataset_selection_bootstraps_from_the_flat_task_tree(tmp_path):
    group = tmp_path / "Group"
    group.mkdir()
    (group / "Group_Thm.tla").write_text("---- MODULE Group_Thm ----\nTHEOREM TRUE\nPROOF OBVIOUS\n====\n")
    (group / "Shared.tla").write_text("---- MODULE Shared ----\nOp == 1\n====\n")
    assert load_dataset_task_keys(str(tmp_path)) == {"Group/Group_Thm.tla"}


def test_dataset_selection_prefers_an_existing_manifest(tmp_path):
    (tmp_path / "manifest.json").write_text(
        json.dumps({"Group/Group_Thm.tla": {"spec_id": "Fixture.tla", "context": [], "reference_proof_steps": 0}})
    )
    (tmp_path / "Stray.tla").write_text("---- MODULE Stray ----\nTHEOREM TRUE\n====\n")
    assert load_dataset_task_keys(str(tmp_path)) == {"Group/Group_Thm.tla"}


def test_dataset_selection_uses_complete_manifest_without_scanning_extra_flat_tasks(tmp_path):
    """Once migration is complete, the manifest is the whole dataset index."""
    (tmp_path / "manifest.json").write_text(
        json.dumps(
            {
                "Group/Group_Thm.tla": {
                    "spec_id": "Fixture.tla",
                    "context": ["Group/Group_ThmScaffold.tla"],
                    "reference_proof_steps": 0,
                }
            }
        )
    )
    benor = tmp_path / "BenOr"
    benor.mkdir()
    (benor / "BenOr_Agreement.tla").write_text("---- MODULE BenOr_Agreement ----\nTHEOREM TRUE\nPROOF OBVIOUS\n====\n")
    assert load_dataset_task_keys(str(tmp_path)) == {"Group/Group_Thm.tla"}


def test_dataset_selection_does_not_recount_manifest_context_layers(tmp_path):
    """A read-only Scaffold layer states preceding lemmas, so it matches the
    task-file rule — but the manifest already names it as context, so it must not
    be mistaken for an un-migrated task."""
    (tmp_path / "manifest.json").write_text(
        json.dumps(
            {
                "Group/Group_Thm.tla": {
                    "spec_id": "Fixture.tla",
                    "context": ["Group/Group_ThmScaffold.tla"],
                    "reference_proof_steps": 0,
                }
            }
        )
    )
    group = tmp_path / "Group"
    group.mkdir()
    (group / "Group_ThmScaffold.tla").write_text(
        "---- MODULE Group_ThmScaffold ----\nLEMMA Earlier == TRUE\nPROOF OBVIOUS\n====\n"
    )
    assert load_dataset_task_keys(str(tmp_path)) == {"Group/Group_Thm.tla"}


def _emit_task(root, subdir, module, statement="THEOREM Thm == TRUE"):
    directory = root / subdir
    directory.mkdir(parents=True, exist_ok=True)
    scaffold = f"{module}Scaffold"
    (directory / f"{scaffold}.tla").write_text(f"---- MODULE {scaffold} ----\nGiven == TRUE\n====\n")
    (directory / f"{module}.tla").write_text(build_task_module(module, scaffold, statement))
    return f"{subdir}/{module}.tla", {
        "spec_id": "Fixture.tla",
        "context": [f"{subdir}/{scaffold}.tla"],
        "reference_proof_steps": 0,
    }


def _finalize(root, manifest, audit_state=None, **kwargs):
    with open(root / "audit.log", "w", encoding="utf-8") as audit:
        return _finalize_layered(_engine(), str(root), manifest, audit_state or {}, audit, run_gates=False, **kwargs)


def test_finalize_writes_a_manifest_the_evaluator_can_load(tmp_path):
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    assert _finalize(tmp_path, {key: entry}) == 1

    boundaries = load_proof_completion_manifest(tmp_path)
    assert set(boundaries) == {key}
    assert [path.name for path in boundaries[key].context_paths] == ["Group_ThmScaffold.tla"]


def test_finalize_sweeps_context_no_task_references(tmp_path):
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    orphan = tmp_path / "Group" / "Group_OldScaffold.tla"
    orphan.write_text("---- MODULE Group_OldScaffold ----\n====\n")
    _finalize(tmp_path, {key: entry})
    assert not orphan.exists(), "a layer left over from a previous generation must not ship"


def test_finalize_fails_when_the_triviality_gate_cannot_judge_a_task(tmp_path, monkeypatch):
    """A second timeout (or an unresolved module) makes the gate return the task
    as `errored`. Finalization must then fail and write no manifest, rather than
    keeping a task the gate never actually judged — the resource-contention case
    the reviewer flagged."""
    import dataset.proof_from_scratch.generate as engine

    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    monkeypatch.setattr(engine, "layered_sany_gate", lambda *a, **k: [])
    monkeypatch.setattr(engine, "layered_triviality_gate", lambda *a, **k: ([], [], [key]))

    with open(tmp_path / "audit.log", "w", encoding="utf-8") as audit, pytest.raises(SystemExit) as excinfo:
        _finalize_layered(engine, str(tmp_path), {key: entry}, {}, audit, run_gates=True)

    assert excinfo.value.code != 0
    assert not (tmp_path / "manifest.json").exists(), "an unjudged task must not be shipped"
    assert "triviality gate could not reach a verdict" in (tmp_path / "audit.log").read_text()


def test_finalize_fails_when_the_regeneration_loses_a_reviewed_task(tmp_path, capsys):
    """A task in the reviewed selection that this run did not regenerate is
    fatal: shipping the shrunken manifest would silently drop it."""
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    with pytest.raises(SystemExit) as excinfo:
        _finalize(tmp_path, {key: entry}, reference_task_keys={key, "Group/Group_Gone.tla"})

    assert excinfo.value.code != 0
    assert "1 missing" in capsys.readouterr().out
    assert not (tmp_path / "manifest.json").exists(), "a run that lost a task must not publish a manifest"
    audit = (tmp_path / "audit.log").read_text()
    assert "Group/Group_Gone.tla: existing dataset task was not regenerated" in audit


def test_finalize_checks_the_selection_before_running_any_gate(tmp_path, monkeypatch):
    import dataset.proof_completion.generate as completion
    import dataset.proof_from_scratch.generate as engine

    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    calls = []
    monkeypatch.setattr(completion, "drop_known_degenerate", lambda *args: calls.append("known") or [])
    monkeypatch.setattr(completion, "layered_duplicate_gate", lambda *args: calls.append("duplicate") or ([], []))
    monkeypatch.setattr(engine, "layered_sany_gate", lambda *args: calls.append("sany") or [])
    monkeypatch.setattr(engine, "layered_triviality_gate", lambda *args: calls.append("triviality") or ([], [], []))

    with open(tmp_path / "audit.log", "w", encoding="utf-8") as audit, pytest.raises(SystemExit):
        _finalize_layered(
            engine,
            str(tmp_path),
            {key: entry},
            {},
            audit,
            run_gates=True,
            reference_task_keys={key, "Group/Group_Missing.tla"},
        )

    assert calls == []


def test_finalize_fails_when_the_regeneration_adds_an_unreviewed_task(tmp_path):
    """A task not in the reviewed selection is fatal too: it expands the
    benchmark past what was reviewed."""
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    with pytest.raises(SystemExit):
        _finalize(tmp_path, {key: entry}, reference_task_keys={"Group/Group_Other.tla"})

    assert not (tmp_path / "manifest.json").exists()
    audit = (tmp_path / "audit.log").read_text()
    assert "Group/Group_Thm.tla: generated task is not in the existing dataset selection" in audit


def test_finalize_accepts_a_run_that_reproduces_the_reviewed_selection(tmp_path):
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    assert _finalize(tmp_path, {key: entry}, reference_task_keys={key}) == 1
    assert (tmp_path / "manifest.json").exists()


def test_finalize_accepts_a_reviewed_task_dropped_by_the_triviality_gate(tmp_path, monkeypatch):
    import dataset.proof_from_scratch.generate as engine

    kept, kept_entry = _emit_task(tmp_path, "Group", "Group_Kept")
    degenerate, degenerate_entry = _emit_task(tmp_path, "Group", "Group_Degenerate")
    manifest = {kept: kept_entry, degenerate: degenerate_entry}

    def drop_degenerate(root, current, audit):
        del current[degenerate]
        (Path(root) / degenerate).unlink()
        audit.write(f"[audit] {degenerate}: placeholder proof verifies — removed\n")
        return [degenerate], [], []

    monkeypatch.setattr(engine, "layered_sany_gate", lambda *args, **kwargs: [])
    monkeypatch.setattr(engine, "layered_triviality_gate", drop_degenerate)

    with open(tmp_path / "audit.log", "w", encoding="utf-8") as audit:
        count = _finalize_layered(
            engine,
            str(tmp_path),
            manifest,
            {},
            audit,
            run_gates=True,
            reference_task_keys={kept, degenerate},
        )

    assert count == 1
    assert set(json.loads((tmp_path / "manifest.json").read_text())) == {kept}
    assert not (tmp_path / degenerate).exists()


def test_seed_staging_copies_the_current_dataset_verbatim(tmp_path):
    """A --filter run must keep the tasks it does not regenerate, so staging
    starts as a byte-for-byte copy of the shipped dataset — files, nested
    directories, and the manifest alike."""
    source = tmp_path / "dataset"
    (source / "Group").mkdir(parents=True)
    (source / "Group" / "Group_Thm.tla").write_text("theorem body")
    (source / "manifest.json").write_text(
        '{"Group/Group_Thm.tla": {"spec_id": "Fixture.tla", "context": [], "reference_proof_steps": 0}}'
    )
    staging = tmp_path / "staging"
    staging.mkdir()

    _seed_staging(str(source), str(staging))

    assert (staging / "Group" / "Group_Thm.tla").read_text() == "theorem body"
    assert (
        staging / "manifest.json"
    ).read_text() == '{"Group/Group_Thm.tla": {"spec_id": "Fixture.tla", "context": [], "reference_proof_steps": 0}}'


def test_filtered_finalization_keeps_tasks_outside_the_filter(tmp_path):
    untouched, untouched_entry = _emit_task(tmp_path, "Other", "Other_Thm")
    regenerated, old_regenerated_entry = _emit_task(tmp_path, "Selected", "Selected_Thm", "THEOREM Old == TRUE")
    untouched_task = (tmp_path / untouched).read_text()
    untouched_context = (tmp_path / untouched_entry["context"][0]).read_text()
    (tmp_path / "manifest.json").write_text(
        json.dumps({untouched: untouched_entry, regenerated: old_regenerated_entry}, indent=2)
    )

    regenerated, regenerated_entry = _emit_task(tmp_path, "Selected", "Selected_Thm", "THEOREM New == TRUE")
    all_bases = {"Other": {"Other"}, "Selected": {"Selected"}}
    _finalize(
        tmp_path,
        {regenerated: regenerated_entry},
        incremental=True,
        scope=(all_bases, {"Selected": {"Selected"}}),
        reference_task_keys={untouched, regenerated},
    )

    written = json.loads((tmp_path / "manifest.json").read_text())
    assert set(written) == {untouched, regenerated}
    assert (tmp_path / untouched).read_text() == untouched_task
    assert (tmp_path / untouched_entry["context"][0]).read_text() == untouched_context


def test_promote_dataset_swaps_staging_over_the_old_dataset(tmp_path):
    output = tmp_path / "dataset"
    output.mkdir()
    (output / "old.tla").write_text("stale")
    staging = tmp_path / "staging"
    staging.mkdir()
    (staging / "new.tla").write_text("fresh")

    _promote_dataset(str(staging), str(output))

    assert (output / "new.tla").read_text() == "fresh"
    assert not (output / "old.tla").exists(), "the previous dataset is fully replaced, not merged"
    assert not staging.exists(), "staging is consumed by the promotion"


def test_promote_dataset_restores_the_old_dataset_when_the_swap_fails(tmp_path, monkeypatch):
    """The promotion moves the old dataset aside before renaming staging in. If
    that rename fails, the old dataset must be put back so a failed run leaves it
    byte-for-byte unchanged."""
    import os as _os

    output = tmp_path / "dataset"
    output.mkdir()
    (output / "keep.tla").write_text("precious")
    staging = tmp_path / "staging"
    staging.mkdir()
    (staging / "new.tla").write_text("fresh")

    real_rename = _os.rename
    calls = {"n": 0}

    def flaky_rename(src, dst):
        calls["n"] += 1
        if calls["n"] == 2:  # the staging -> output rename
            raise OSError("simulated cross-device or race failure")
        return real_rename(src, dst)

    monkeypatch.setattr("dataset.proof_completion.generate.os.rename", flaky_rename)

    with pytest.raises(OSError):
        _promote_dataset(str(staging), str(output))

    assert (output / "keep.tla").read_text() == "precious", "a failed swap must not lose the existing dataset"


def test_finalize_flags_a_scaffold_two_tasks_share(tmp_path):
    first, entry = _emit_task(tmp_path, "Group", "Group_One")
    # A second task built against the FIRST task's scaffold — the leak this
    # audit exists to catch: one target's givens must not reach another task.
    second = "Group/Group_Two.tla"
    (tmp_path / "Group" / "Group_Two.tla").write_text(
        build_task_module("Group_Two", "Group_OneScaffold", "THEOREM Other == TRUE")
    )
    manifest = {
        first: entry,
        second: {"spec_id": "Fixture.tla", "context": entry["context"], "reference_proof_steps": 0},
    }
    audit_state = {"scaffold_owner": {entry["context"][0]: [first, second]}}
    _finalize(tmp_path, manifest, audit_state)

    audit = (tmp_path / "audit.log").read_text()
    assert "LEAK scaffold Group/Group_OneScaffold.tla is shared by multiple tasks" in audit


SUITE = Path(os.path.dirname(os.path.abspath(__file__))).parents[1] / "benchmark" / "proof-completion"


@pytest.mark.skipif(not (SUITE / "manifest.json").is_file(), reason="proof-completion suite is not layered yet")
def test_shipped_suite_satisfies_the_evaluator_contract():
    """The dataset itself must load under the contract the grader enforces."""
    boundaries = load_proof_completion_manifest(SUITE)
    assert boundaries, "the shipped manifest declares no tasks"

    scaffold_owners = {}
    for task_key, boundary in boundaries.items():
        scaffolds = [path for path in boundary.context_paths if path.name.endswith("Scaffold.tla")]
        assert len(scaffolds) == 1, f"{task_key} must own exactly one scaffold, got {scaffolds}"
        scaffold_owners.setdefault(scaffolds[0], []).append(task_key)

    shared = {path.name: keys for path, keys in scaffold_owners.items() if len(keys) > 1}
    assert not shared, f"a target's scaffolding must belong to exactly one task: {shared}"


def test_finalize_refuses_to_write_a_manifest_after_a_generation_error(tmp_path):
    """A source that failed to parse must fail the run, not shrink the dataset.

    Regression: a nonexistent source file logged its SANY error, exited 0 and
    wrote an EMPTY manifest — the audit trail said "broken" while the artifact
    said "this is the dataset".
    """
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    audit_state = {"errors": ["source/Nope/Nope.tla: SANY parse failed — no such file"]}
    with pytest.raises(SystemExit) as excinfo:
        _finalize(tmp_path, {key: entry}, audit_state)

    assert excinfo.value.code != 0
    assert not (tmp_path / "manifest.json").exists(), "a failed run must not publish a manifest"
    audit = (tmp_path / "audit.log").read_text()
    assert "generation error: source/Nope/Nope.tla" in audit
    assert "manifest not written" in audit


def test_finalize_refuses_an_empty_generation(tmp_path):
    with pytest.raises(SystemExit):
        _finalize(tmp_path, {})
    assert not (tmp_path / "manifest.json").exists()


def test_finalize_keeps_context_a_failing_run_would_have_swept(tmp_path):
    """The sweep DELETES files; a run that is about to fail must not prune."""
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    orphan = tmp_path / "Group" / "Group_OldScaffold.tla"
    orphan.write_text("---- MODULE Group_OldScaffold ----\n====\n")
    with pytest.raises(SystemExit):
        _finalize(tmp_path, {key: entry}, {"errors": ["boom"]})
    assert orphan.exists()


def test_finalize_refuses_a_manifest_the_evaluator_would_reject(tmp_path):
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    entry = {
        "spec_id": "Fixture.tla",
        "context": [*entry["context"], "Group/Missing.tla"],
        "reference_proof_steps": 0,
    }
    with pytest.raises(ManifestError):
        _finalize(tmp_path, {key: entry})


# --- cross-directory duplicates (#90, in the layered layout) ---------------


def _dup_task(root, subdir, module, scaffold_body="Given == TRUE"):
    directory = root / subdir
    directory.mkdir(parents=True, exist_ok=True)
    scaffold = f"{module}Scaffold"
    (directory / f"{scaffold}.tla").write_text(f"---- MODULE {scaffold} ----\n{scaffold_body}\n====\n")
    (directory / f"{module}.tla").write_text(build_task_module(module, scaffold, "THEOREM Thm == TRUE"))
    return f"{subdir}/{module}.tla", {
        "spec_id": "Fixture.tla",
        "context": [f"{subdir}/{scaffold}.tla"],
        "reference_proof_steps": 0,
    }


def test_an_approved_duplicate_keeps_only_the_canonical_copy(tmp_path):
    """`Sets_*` is vendored under both Data/ (canonical) and Consensus/."""
    canonical, c_entry = _dup_task(tmp_path, "Data", "Sets_PigeonHole")
    copy, copy_entry = _dup_task(tmp_path, "Consensus", "Sets_PigeonHole")
    manifest = {canonical: c_entry, copy: copy_entry}

    removed, unapproved = layered_duplicate_gate(str(tmp_path), manifest, StringIO())

    assert unapproved == []
    assert removed == [copy]
    assert set(manifest) == {canonical}
    assert not (tmp_path / "Consensus" / "Sets_PigeonHole.tla").exists()


def test_an_unapproved_duplicate_is_reported_not_silently_resolved(tmp_path):
    first, first_entry = _dup_task(tmp_path, "GroupA", "Mystery_Thm")
    second, second_entry = _dup_task(tmp_path, "GroupB", "Mystery_Thm")
    manifest = {first: first_entry, second: second_entry}

    removed, unapproved = layered_duplicate_gate(str(tmp_path), manifest, StringIO())

    assert removed == []
    assert unapproved == [sorted([first, second])], "a new collision is a human decision"
    assert set(manifest) == {first, second}


def test_same_named_tasks_with_different_givens_are_not_duplicates(tmp_path):
    """A layered task file is a thin EXTENDS wrapper, so two tasks can match on
    it while resting on different scaffolding — they are different prompts."""
    first, first_entry = _dup_task(tmp_path, "Data", "Sets_PigeonHole", scaffold_body="Given == TRUE")
    second, second_entry = _dup_task(tmp_path, "Consensus", "Sets_PigeonHole", scaffold_body="Given == FALSE")
    manifest = {first: first_entry, second: second_entry}

    removed, unapproved = layered_duplicate_gate(str(tmp_path), manifest, StringIO())

    assert (removed, unapproved) == ([], [])
    assert set(manifest) == {first, second}


def test_finalize_fails_on_an_unapproved_duplicate(tmp_path):
    first, first_entry = _dup_task(tmp_path, "GroupA", "Mystery_Thm")
    second, second_entry = _dup_task(tmp_path, "GroupB", "Mystery_Thm")
    with pytest.raises(SystemExit):
        _finalize(tmp_path, {first: first_entry, second: second_entry})
    assert not (tmp_path / "manifest.json").exists()


# --- recorded degenerate targets -------------------------------------------


def test_a_recorded_degenerate_target_is_dropped(tmp_path):
    """The gate's verdict is not reproducible under its own load, so a task
    measured to verify unchanged is dropped from the record instead."""
    key, entry = _emit_task(tmp_path, "Data", "SequencesTheorems_AppendDef")
    manifest = {key: entry}

    removed = drop_known_degenerate(str(tmp_path), manifest, StringIO())

    assert removed == [key], "the recorded target must not survive a run"
    assert manifest == {}
    assert not (tmp_path / "Data" / "SequencesTheorems_AppendDef.tla").exists()


def test_recorded_targets_leave_every_other_task_alone(tmp_path):
    key, entry = _emit_task(tmp_path, "Data", "SequencesTheorems_ConcatAssociative")
    manifest = {key: entry}

    assert drop_known_degenerate(str(tmp_path), manifest, StringIO()) == []
    assert set(manifest) == {key}


def test_a_recorded_target_absent_from_the_run_is_not_an_error(tmp_path):
    """It may have been dropped by the gate itself, or renamed upstream."""
    assert drop_known_degenerate(str(tmp_path), {}, StringIO()) == []


def test_every_recorded_target_documents_its_measurement():
    """A recorded drop is a human judgement; it must carry its evidence so it
    can be rechecked after a tlapm or backend upgrade."""
    from dataset.proof_completion.generate import _KNOWN_DEGENERATE_PATH

    with open(_KNOWN_DEGENERATE_PATH, encoding="utf-8") as f:
        recorded = json.load(f)["targets"]

    assert recorded, "the record exists to pin known-degenerate tasks"
    for entry in recorded:
        assert entry["task"].endswith(".tla")
        assert entry["reason"].strip()
        assert entry["evidence"].strip()
