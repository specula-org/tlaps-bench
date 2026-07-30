"""SANY-based policy checks for marked proof-from-scratch helpers."""

from __future__ import annotations

import pytest

from common.proof_from_scratch_contract import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
)
from tlacheck.context import CheckContext
from tlacheck.engine import run_rules
from tlacheck.rules import helper_region
from tlacore.model import (
    Assumption,
    Instance,
    Loc,
    Module,
    ModuleDirective,
    Operator,
    Symbol,
    Theorem,
    TopLevelNode,
)
from tlacore.provenance import Provenance
from tlacore.sany.dump import SanyError, dump_normalized


def _source(helper: str, proof: str = "PROOF OBVIOUS") -> str:
    return "\n".join(
        (
            "---- MODULE Task ----",
            "EXTENDS Model",
            BEGIN_AGENT_HELPERS,
            helper,
            END_AGENT_HELPERS,
            "THEOREM Target == TRUE",
            BEGIN_AGENT_PROOF,
            proof,
            END_AGENT_PROOF,
            "====",
            "",
        )
    )


def _module(**overrides) -> Module:
    values = {
        "name": "Task",
        "source_file": "Task.tla",
        "filename": "Task.tla",
        "line_start": 1,
        "line_end": 10,
        "extends": ["Model"],
        "constants": [],
        "variables": [],
        "assumes": [],
        "instances": [],
        "operators": [],
        "spec_formulas": [],
        "theorems": [],
    }
    values.update(overrides)
    return Module(**values)


def _context(helper: str, module: Module, proof: str = "PROOF OBVIOUS") -> CheckContext:
    source = _source(helper, proof)
    return CheckContext(
        target_name="Task",
        solution_dir=".",
        solution=module,
        baseline=_module(),
        provenance=Provenance(target="Task"),
        solution_source=source,
        baseline_source=source,
    )


def _proof_only_source(proof: str = "PROOF OBVIOUS") -> str:
    return "\n".join(
        (
            "---- MODULE Task ----",
            "EXTENDS Model",
            "THEOREM Target == TRUE",
            BEGIN_AGENT_PROOF,
            proof,
            END_AGENT_PROOF,
            "====",
            "",
        )
    )


def _proof_only_context(module: Module, proof: str = "PROOF OBVIOUS") -> CheckContext:
    source = _proof_only_source(proof)
    return CheckContext(
        target_name="Task",
        solution_dir=".",
        solution=module,
        baseline=_module(),
        provenance=Provenance(target="Task"),
        solution_source=source,
        baseline_source=source,
    )


@pytest.mark.parametrize(
    ("field", "declaration", "kind"),
    [
        ("constants", Symbol("C", Loc(4, 1, 4, 10)), "CONSTANT"),
        ("variables", Symbol("v", Loc(4, 1, 4, 10)), "VARIABLE"),
        ("assumes", Assumption("A", False, Loc(4, 1, 4, 20), []), "ASSUME/AXIOM"),
        ("instances", Instance("I", "Other", Loc(4, 1, 4, 20), []), "INSTANCE"),
    ],
)
def test_rejects_forbidden_declaration_kinds(field, declaration, kind):
    issues = helper_region.check(_context("forbidden declaration", _module(**{field: [declaration]})))

    assert len(issues) == 1
    assert issues[0].vector == "HELPER_REGION_VIOLATION"
    assert kind in issues[0].message


def test_allows_fresh_operator_and_fully_proved_named_lemma():
    operator = Operator("Fresh", Loc(4, 1, 4, 13), False, None, [])
    lemma = Theorem(
        name="Helper",
        loc=Loc(4, 1, 4, 30),
        statement_loc=Loc(4, 17, 4, 20),
        proof_loc=Loc(4, 22, 4, 30),
        proof_is_omitted=False,
        references=[],
        statement_references=[],
        shape={},
    )

    issues = helper_region.check(
        _context("Fresh == TRUE  LEMMA Helper == TRUE PROOF OBVIOUS", _module(operators=[operator], theorems=[lemma]))
    )

    assert issues == []


def test_allows_use_and_hide_def_directives():
    directives = [
        ModuleDirective("USE", True, Loc(4, 1, 4, 11)),
        ModuleDirective("HIDE", True, Loc(5, 1, 5, 12)),
    ]

    assert helper_region.check(_context("USE DEF Foo\nHIDE DEF Bar", _module(directives=directives))) == []


def test_rejects_module_level_use_of_a_fact():
    directive = ModuleDirective("USE", False, Loc(4, 1, 4, 7))

    issues = helper_region.check(_context("USE Fact", _module(directives=[directive])))

    assert len(issues) == 1
    assert "must use DEF" in issues[0].message


@pytest.mark.parametrize(
    "theorem",
    [
        Theorem(None, Loc(4, 1, 4, 30), Loc(4, 9, 4, 12), Loc(4, 14, 4, 30), False, [], [], {}),
        Theorem("Helper", Loc(4, 1, 4, 20), Loc(4, 11, 4, 15), None, False, [], [], {}),
        Theorem("Helper", Loc(4, 1, 4, 30), Loc(4, 11, 4, 15), Loc(4, 17, 4, 30), True, [], [], {}),
    ],
)
def test_rejects_unnamed_or_admitted_helper_lemmas(theorem):
    issues = helper_region.check(_context("THEOREM helper", _module(theorems=[theorem])))

    assert issues
    assert all(issue.vector == "HELPER_REGION_VIOLATION" for issue in issues)


def test_ignores_fixed_declarations_outside_helper_region():
    constant = Symbol("Given", Loc(2, 1, 2, 14))

    assert helper_region.check(_context("USE DEF Foo", _module(constants=[constant]))) == []


def test_rejects_helper_declaration_crossing_region_boundary():
    operator = Operator("Crossing", Loc(4, 1, 6, 12), False, None, [])

    issues = helper_region.check(_context("Crossing == TRUE", _module(operators=[operator])))

    assert len(issues) == 1
    assert "must be contained in the helper region" in issues[0].message


@pytest.mark.parametrize(
    ("field", "declaration"),
    [
        ("constants", Symbol("C", Loc(8, 1, 8, 10))),
        ("variables", Symbol("v", Loc(8, 1, 8, 10))),
        ("assumes", Assumption("A", False, Loc(8, 1, 8, 20), [])),
        ("instances", Instance("I", "Other", Loc(8, 1, 8, 20), [])),
        ("operators", Operator("Late", Loc(8, 1, 8, 12), False, None, [])),
        (
            "theorems",
            Theorem("Late", Loc(8, 1, 8, 30), Loc(8, 9, 8, 12), Loc(8, 14, 8, 30), False, [], [], {}),
        ),
        ("inner_modules", Symbol("Inner", Loc(8, 1, 8, 24))),
        ("directives", ModuleDirective("USE", True, Loc(8, 1, 8, 11))),
        ("other_top_levels", TopLevelNode("UnexpectedNode", Loc(8, 1, 8, 12))),
    ],
)
def test_rejects_module_declarations_in_proof_region(field, declaration):
    issues = helper_region.check(_context("", _module(**{field: [declaration]})))

    assert len(issues) == 1
    assert "not allowed in the proof region" in issues[0].message


def test_proof_only_contract_rejects_module_declaration_in_proof_region():
    operator = Operator("Late", Loc(6, 1, 6, 12), False, None, [])
    context = _proof_only_context(_module(operators=[operator]), "PROOF OBVIOUS\nLate == TRUE")

    issues = helper_region.check(context)

    assert len(issues) == 1
    assert "module-level operator declarations are not allowed in the proof region" in issues[0].message


def test_proof_only_contract_allows_proof_local_define_and_use(tmp_path):
    model = tmp_path / "Model.tla"
    task = tmp_path / "Task.tla"
    model.write_text("---- MODULE Model ----\nTHEOREM Fact == TRUE\nPROOF OBVIOUS\n====\n")
    proof = "PROOF\n<1>1. DEFINE StepFact == TRUE\n<1>2. USE Fact\n<1>3. QED BY StepFact"
    task.write_text(_proof_only_source(proof))
    module = dump_normalized(str(task), dep_dir=str(tmp_path))

    assert "StepFact" not in {operator.name for operator in module.operators}
    assert module.directives == []
    assert helper_region.check(_proof_only_context(module, proof)) == []


def test_proof_bounds_match_sany_when_helper_comment_contains_form_feed(tmp_path):
    model = tmp_path / "Model.tla"
    task = tmp_path / "Task.tla"
    helper = "\\* padding\fcontinuation"
    proof = "PROOF OBVIOUS  CONSTANT C"
    model.write_text("---- MODULE Model ----\n====\n")
    task.write_text(_source(helper, proof))

    module = dump_normalized(str(task), dep_dir=str(tmp_path))
    issues = helper_region.check(_context(helper, module, proof))

    assert [constant.loc.line_start for constant in module.constants] == [8]
    assert len(issues) == 1
    assert "module-level CONSTANT declarations are not allowed in the proof region" in issues[0].message


def test_rejects_nested_module():
    inner = Symbol("Inner", Loc(4, 1, 5, 4))
    issues = helper_region.check(_context("---- MODULE Inner ----\n====", _module(inner_modules=[inner])))

    assert len(issues) == 1
    assert "nested modules" in issues[0].message


def test_rejects_unclassified_top_level_declaration():
    node = TopLevelNode("UnexpectedNode", Loc(4, 1, 4, 12))

    issues = helper_region.check(_context("unexpected declaration", _module(other_top_levels=[node])))

    assert len(issues) == 1
    assert "unclassified top-level" in issues[0].message


def test_unmarked_legacy_task_is_out_of_scope():
    context = _context("", _module(constants=[Symbol("C", Loc(4, 1, 4, 10))]))
    context.baseline_source = "---- MODULE Task ----\n====\n"

    assert helper_region.check(context) == []


def test_rule_is_wired_into_sany_engine():
    context = _context("CONSTANT C", _module(constants=[Symbol("C", Loc(4, 1, 4, 10))]))

    assert "HELPER_REGION_VIOLATION" in {issue.vector for issue in run_rules(context)}


@pytest.mark.parametrize(
    "helper",
    [
        "ContextValue == TRUE",
        "ContextValue == FALSE",
        "LOCAL ContextValue == TRUE",
        "LEMMA ContextValue == TRUE\nPROOF OBVIOUS",
    ],
)
def test_exact_context_sany_rejects_shadowed_helper_name(tmp_path, helper):
    model = tmp_path / "Model.tla"
    task = tmp_path / "Task.tla"
    model.write_text("---- MODULE Model ----\nContextValue == FALSE\n====\n")
    task.write_text(_source(helper))

    with pytest.raises(SanyError, match="SANY parse error"):
        dump_normalized(str(task), dep_dir=str(tmp_path))


def test_proof_step_definition_is_not_a_module_operator(tmp_path):
    model = tmp_path / "Model.tla"
    task = tmp_path / "Task.tla"
    model.write_text("---- MODULE Model ----\n====\n")
    proof = "PROOF\n<1>1. DEFINE StepFact == TRUE\n<1>2. QED OBVIOUS"
    task.write_text(_source("").replace("PROOF OBVIOUS", proof))

    module = dump_normalized(str(task), dep_dir=str(tmp_path))

    assert "StepFact" not in {operator.name for operator in module.operators}


def test_sany_classifies_local_and_recursive_helpers_as_operators(tmp_path):
    model = tmp_path / "Model.tla"
    task = tmp_path / "Task.tla"
    model.write_text("---- MODULE Model ----\n====\n")
    helper = "\n".join(
        (
            "LOCAL Fresh == TRUE",
            "RECURSIVE Loop(_)",
            "Loop(value) == IF value THEN TRUE ELSE Loop(TRUE)",
        )
    )
    task.write_text(_source(helper))

    module = dump_normalized(str(task), dep_dir=str(tmp_path))

    assert {"Fresh", "Loop"} <= {operator.name for operator in module.operators}
    assert module.other_top_levels == []


def test_proof_directive_inside_helper_lemma_is_not_module_level(tmp_path):
    model = tmp_path / "Model.tla"
    task = tmp_path / "Task.tla"
    model.write_text("---- MODULE Model ----\nContextValue == TRUE\n====\n")
    helper = "LEMMA Helper == TRUE\nPROOF\n<1>1. USE ContextValue\n<1>2. QED OBVIOUS"
    task.write_text(_source(helper))

    module = dump_normalized(str(task), dep_dir=str(tmp_path))

    assert module.directives == []
    assert helper_region.check(_context(helper, module)) == []


def test_sany_classifies_module_directives(tmp_path):
    model = tmp_path / "Model.tla"
    task = tmp_path / "Task.tla"
    model.write_text(
        "---- MODULE Model ----\nContextValue == FALSE\nTHEOREM ContextFact == TRUE\nPROOF OBVIOUS\n====\n"
    )
    task.write_text(_source("USE DEF ContextValue\nHIDE DEF ContextValue"))

    module = dump_normalized(str(task), dep_dir=str(tmp_path))

    assert [(directive.kind, directive.definitions_only) for directive in module.directives] == [
        ("USE", True),
        ("HIDE", True),
    ]

    task.write_text(_source("USE ContextValue"))
    module = dump_normalized(str(task), dep_dir=str(tmp_path))

    assert [(directive.kind, directive.definitions_only) for directive in module.directives] == [("USE", False)]

    task.write_text(_source("HIDE ContextFact"))
    module = dump_normalized(str(task), dep_dir=str(tmp_path))

    assert [(directive.kind, directive.definitions_only) for directive in module.directives] == [("HIDE", False)]


def test_sany_classifies_nested_module(tmp_path):
    model = tmp_path / "Model.tla"
    task = tmp_path / "Task.tla"
    model.write_text("---- MODULE Model ----\n====\n")
    task.write_text(
        _source("  ---- MODULE Inner ----\n  InnerValue == TRUE\n  ========================\n------------------------")
    )

    module = dump_normalized(str(task), dep_dir=str(tmp_path))

    assert [inner.name for inner in module.inner_modules] == ["Inner"]
