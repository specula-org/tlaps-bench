"""Strict proof-completion manifest and proof-region contract."""

from __future__ import annotations

import json

import pytest

from common.proof_completion_contract import (
    BEGIN_AGENT_PROOF,
    END_AGENT_PROOF,
    EditableRegionError,
    ManifestError,
    load_proof_completion_manifest,
    parse_proof_region,
)
from common.proof_from_scratch_contract import BEGIN_AGENT_HELPERS, END_AGENT_HELPERS


def _write_module(root, relative_path, *, body=""):
    path = root / relative_path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"---- MODULE {path.stem} ----\n{body}====\n", encoding="utf-8")
    return path.resolve()


def _write_task(root, relative_path, *, body=""):
    return _write_module(
        root,
        relative_path,
        body=(f"{body}THEOREM Target == TRUE\n{BEGIN_AGENT_PROOF}\nPROOF OBVIOUS\n{END_AGENT_PROOF}\n"),
    )


def _write_manifest(root, manifest):
    root.mkdir(parents=True, exist_ok=True)
    (root / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")


def _source(newline="\n"):
    return newline.join(
        (
            "---- MODULE Task ----",
            "EXTENDS Model, Scaffold",
            "THEOREM Target == TRUE",
            BEGIN_AGENT_PROOF,
            "PROOF OBVIOUS",
            END_AGENT_PROOF,
            "====",
            "",
        )
    )


def test_loads_sorted_tasks_and_preserves_exact_context_order(tmp_path):
    suite = tmp_path / "proof-completion"
    task_z = _write_task(suite, "Zed/Zed_Target.tla")
    task_a = _write_task(suite, "Alpha/Alpha_Target.tla", body="EXTENDS Model, Scaffold\n")
    scaffold = _write_module(suite, "Context/Scaffold.tla")
    model = _write_module(suite, "Context/Model.tla")
    _write_manifest(
        suite,
        {
            "Zed/Zed_Target.tla": {"context": []},
            "Alpha/Alpha_Target.tla": {
                "context": ["Context/Scaffold.tla", "Context/Model.tla"],
            },
        },
    )

    boundaries = load_proof_completion_manifest(suite)

    assert list(boundaries) == ["Alpha/Alpha_Target.tla", "Zed/Zed_Target.tla"]
    assert boundaries["Alpha/Alpha_Target.tla"].task_path == task_a
    assert boundaries["Alpha/Alpha_Target.tla"].context_paths == (scaffold, model)
    assert boundaries["Zed/Zed_Target.tla"].task_path == task_z


def test_task_requires_exact_proof_markers(tmp_path):
    suite = tmp_path / "proof-completion"
    _write_module(suite, "Task.tla", body="THEOREM Target == TRUE\nPROOF OBVIOUS\n")
    _write_manifest(suite, {"Task.tla": {"context": []}})

    with pytest.raises(ManifestError, match="Task.tla.*invalid editable regions"):
        load_proof_completion_manifest(suite)


def test_task_cannot_expose_a_helper_region(tmp_path):
    suite = tmp_path / "proof-completion"
    _write_task(
        suite,
        "Task.tla",
        body=f"{BEGIN_AGENT_HELPERS}\nHelper == TRUE\n{END_AGENT_HELPERS}\n",
    )
    _write_manifest(suite, {"Task.tla": {"context": []}})

    with pytest.raises(ManifestError, match="must not contain an AGENT HELPERS region"):
        load_proof_completion_manifest(suite)


def test_manifest_context_must_cover_transitive_references(tmp_path):
    suite = tmp_path / "proof-completion"
    _write_task(suite, "Task.tla", body="EXTENDS Model\n")
    _write_module(suite, "Model.tla", body="EXTENDS Missing\n")
    _write_module(suite, "Missing.tla")
    _write_manifest(suite, {"Task.tla": {"context": ["Model.tla"]}})

    with pytest.raises(ManifestError, match="incomplete context.*Missing"):
        load_proof_completion_manifest(suite)


def test_parse_proof_region_preserves_fixed_and_editable_bytes():
    source = _source()

    region = parse_proof_region(source)

    assert region.fixed_prefix.endswith(f"THEOREM Target == TRUE\n{BEGIN_AGENT_PROOF}\n")
    assert region.proof == "PROOF OBVIOUS\n"
    assert region.fixed_suffix == f"{END_AGENT_PROOF}\n====\n"
    assert region.proof_line_bounds == (5, 5)
    assert region.render() == source
    assert region.render(proof="PROOF BY TRUE\n") == source.replace("PROOF OBVIOUS", "PROOF BY TRUE")


def test_parse_proof_region_preserves_crlf_and_sany_line_bounds():
    source = _source("\r\n").replace("PROOF OBVIOUS", "\\* padding\fcontinuation")

    region = parse_proof_region(source)

    assert region.proof == "\\* padding\fcontinuation\r\n"
    assert region.fixed_prefix.endswith(f"{BEGIN_AGENT_PROOF}\r\n")
    assert region.fixed_suffix.startswith(f"{END_AGENT_PROOF}\r\n")
    assert region.proof_line_bounds == (5, 5)
    assert region.render() == source


@pytest.mark.parametrize("marker", [BEGIN_AGENT_PROOF, END_AGENT_PROOF])
def test_missing_or_duplicate_proof_marker_is_rejected(marker):
    missing = _source().replace(f"{marker}\n", "", 1)
    duplicate = _source().replace(f"{marker}\n", f"{marker}\n{marker}\n", 1)

    with pytest.raises(EditableRegionError, match="exactly once, found 0"):
        parse_proof_region(missing)
    with pytest.raises(EditableRegionError, match="exactly once, found 2"):
        parse_proof_region(duplicate)
