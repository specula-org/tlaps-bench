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
    build_scaffold,
    build_task_module,
    dependency_module_text,
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
    (tmp_path / "manifest.json").write_text(json.dumps({"Group/Group_Thm.tla": {"context": []}}))
    (tmp_path / "Stray.tla").write_text("---- MODULE Stray ----\nTHEOREM TRUE\n====\n")
    assert load_dataset_task_keys(str(tmp_path)) == {"Group/Group_Thm.tla"}


def _emit_task(root, subdir, module, statement="THEOREM Thm == TRUE"):
    directory = root / subdir
    directory.mkdir(parents=True, exist_ok=True)
    scaffold = f"{module}Scaffold"
    (directory / f"{scaffold}.tla").write_text(f"---- MODULE {scaffold} ----\nGiven == TRUE\n====\n")
    (directory / f"{module}.tla").write_text(build_task_module(module, scaffold, statement))
    return f"{subdir}/{module}.tla", {"context": [f"{subdir}/{scaffold}.tla"]}


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


def test_finalize_reports_tasks_the_regeneration_lost(tmp_path, capsys):
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    _finalize(tmp_path, {key: entry}, reference_task_keys={key, "Group/Group_Gone.tla"})

    assert "1 missing" in capsys.readouterr().out
    audit = (tmp_path / "audit.log").read_text()
    assert "Group/Group_Gone.tla: existing dataset task was not regenerated" in audit


def test_finalize_flags_a_scaffold_two_tasks_share(tmp_path):
    first, entry = _emit_task(tmp_path, "Group", "Group_One")
    # A second task built against the FIRST task's scaffold — the leak this
    # audit exists to catch: one target's givens must not reach another task.
    second = "Group/Group_Two.tla"
    (tmp_path / "Group" / "Group_Two.tla").write_text(
        build_task_module("Group_Two", "Group_OneScaffold", "THEOREM Other == TRUE")
    )
    manifest = {first: entry, second: {"context": entry["context"]}}
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


def test_finalize_refuses_a_manifest_the_evaluator_would_reject(tmp_path):
    key, entry = _emit_task(tmp_path, "Group", "Group_Thm")
    entry = {"context": [*entry["context"], "Group/Missing.tla"]}
    with pytest.raises(ManifestError):
        _finalize(tmp_path, {key: entry})
