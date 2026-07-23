"""Tests for the proof-from-scratch manifest and editable-region contract."""

from __future__ import annotations

import json
from dataclasses import FrozenInstanceError

import pytest

from common.proof_from_scratch_contract import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
    EditableRegionError,
    ManifestError,
    load_proof_from_scratch_manifest,
    parse_editable_regions,
)


def _write_module(root, relative_path, *, declared_name=None, body=""):
    path = root / relative_path
    path.parent.mkdir(parents=True, exist_ok=True)
    module_name = declared_name if declared_name is not None else path.stem
    path.write_text(f"---- MODULE {module_name} ----\n{body}====\n", encoding="utf-8")
    return path.resolve()


def _write_manifest(root, value):
    root.mkdir(parents=True, exist_ok=True)
    (root / "manifest.json").write_text(json.dumps(value), encoding="utf-8")


def _canonical_source(newline="\n"):
    return newline.join(
        (
            "---- MODULE Task ----",
            "EXTENDS TaskDefs",
            "",
            BEGIN_AGENT_HELPERS,
            "Helper == TRUE",
            END_AGENT_HELPERS,
            "",
            "THEOREM Target == TRUE",
            BEGIN_AGENT_PROOF,
            "PROOF OBVIOUS",
            END_AGENT_PROOF,
            "====",
            "",
        )
    )


def test_loads_sorted_immutable_boundaries_and_preserves_context_order(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    target_z = _write_module(suite, "Zed/Zed_Target.tla")
    target_a = _write_module(suite, "Alpha/Alpha_Target.tla")
    context_z = _write_module(suite, "Shared/ZContext.tla")
    context_a = _write_module(suite, "Shared/AContext.tla")
    _write_manifest(
        suite,
        {
            "Zed/Zed_Target.tla": {"context": []},
            "Alpha/Alpha_Target.tla": {
                "context": ["Shared/ZContext.tla", "Shared/AContext.tla"],
            },
        },
    )

    boundaries = load_proof_from_scratch_manifest(suite)

    assert list(boundaries) == ["Alpha/Alpha_Target.tla", "Zed/Zed_Target.tla"]
    assert boundaries["Alpha/Alpha_Target.tla"].task_path == target_a
    assert boundaries["Alpha/Alpha_Target.tla"].context_paths == (context_z, context_a)
    assert boundaries["Zed/Zed_Target.tla"].task_path == target_z
    with pytest.raises(TypeError):
        boundaries["new"] = boundaries["Alpha/Alpha_Target.tla"]
    with pytest.raises(FrozenInstanceError):
        boundaries["Alpha/Alpha_Target.tla"].task_key = "changed"


def test_missing_manifest_fails_closed(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "Task.tla")

    with pytest.raises(ManifestError, match="missing proof-from-scratch manifest"):
        load_proof_from_scratch_manifest(suite)


def test_malformed_json_is_rejected(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    suite.mkdir()
    (suite / "manifest.json").write_text("{not-json", encoding="utf-8")

    with pytest.raises(ManifestError, match="invalid JSON"):
        load_proof_from_scratch_manifest(suite)


@pytest.mark.parametrize(
    ("manifest", "message"),
    [
        ([], "root must be a JSON object"),
        ({"Task.tla": []}, "object containing only 'context'"),
        ({"Task.tla": {}}, "object containing only 'context'"),
        ({"Task.tla": {"context": [], "extra": True}}, "object containing only 'context'"),
        ({"Task.tla": {"context": {}}}, "field 'context' must be a list"),
        ({"Task.tla": {"context": [7]}}, "context item 0 must be a string"),
    ],
)
def test_invalid_manifest_schema_is_rejected(tmp_path, manifest, message):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "Task.tla")
    _write_manifest(suite, manifest)

    with pytest.raises(ManifestError, match=message):
        load_proof_from_scratch_manifest(suite)


def test_duplicate_json_keys_are_rejected(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    suite.mkdir()
    (suite / "manifest.json").write_text(
        '{"Task.tla":{"context":[]},"Task.tla":{"context":[]}}',
        encoding="utf-8",
    )

    with pytest.raises(ManifestError, match="duplicate JSON object key 'Task.tla'"):
        load_proof_from_scratch_manifest(suite)


@pytest.mark.parametrize(
    "task_key",
    [
        "",
        "/absolute.tla",
        "../escape.tla",
        "Area/../escape.tla",
        "./Task.tla",
        "Area//Task.tla",
        r"Area\Task.tla",
        "Task.txt",
    ],
)
def test_noncanonical_or_unsafe_paths_are_rejected(tmp_path, task_key):
    suite = tmp_path / "proof-from-scratch"
    _write_manifest(suite, {task_key: {"context": []}})

    with pytest.raises(ManifestError):
        load_proof_from_scratch_manifest(suite)


def test_missing_manifest_file_entry_is_rejected(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_manifest(suite, {"Missing.tla": {"context": []}})

    with pytest.raises(ManifestError, match="does not exist"):
        load_proof_from_scratch_manifest(suite)


def test_task_symlink_cannot_escape_suite_root(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    suite.mkdir()
    outside = _write_module(tmp_path, "Escape.tla")
    (suite / "Escape.tla").symlink_to(outside)
    _write_manifest(suite, {"Escape.tla": {"context": []}})

    with pytest.raises(ManifestError, match="escapes the suite root through a symlink"):
        load_proof_from_scratch_manifest(suite)


def test_manifest_symlink_cannot_escape_suite_root(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    suite.mkdir()
    outside = tmp_path / "outside-manifest.json"
    outside.write_text("{}", encoding="utf-8")
    (suite / "manifest.json").symlink_to(outside)

    with pytest.raises(ManifestError, match="manifest escapes the suite root"):
        load_proof_from_scratch_manifest(suite)


def test_duplicate_context_path_is_rejected(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "Task.tla")
    _write_module(suite, "Model.tla")
    _write_manifest(suite, {"Task.tla": {"context": ["Model.tla", "Model.tla"]}})

    with pytest.raises(ManifestError, match="repeats context path 'Model.tla'"):
        load_proof_from_scratch_manifest(suite)


def test_context_aliases_to_same_file_are_rejected(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "Task.tla")
    original = _write_module(suite, "one/Model.tla")
    alias = suite / "two/Model.tla"
    alias.parent.mkdir()
    alias.symlink_to(original)
    _write_manifest(suite, {"Task.tla": {"context": ["one/Model.tla", "two/Model.tla"]}})

    with pytest.raises(ManifestError, match="multiple context paths resolving"):
        load_proof_from_scratch_manifest(suite)


def test_target_cannot_appear_in_its_own_context(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "Task.tla")
    _write_manifest(suite, {"Task.tla": {"context": ["Task.tla"]}})

    with pytest.raises(ManifestError, match="includes itself in its context"):
        load_proof_from_scratch_manifest(suite)


def test_context_cannot_include_another_manifest_task(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "First.tla")
    _write_module(suite, "Second.tla")
    _write_manifest(
        suite,
        {
            "First.tla": {"context": ["Second.tla"]},
            "Second.tla": {"context": []},
        },
    )

    with pytest.raises(ManifestError, match="includes task 'Second.tla' in its context"):
        load_proof_from_scratch_manifest(suite)


def test_duplicate_module_basenames_are_rejected_per_task(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "Task.tla")
    _write_module(suite, "one/Model.tla")
    _write_module(suite, "two/Model.tla")
    _write_manifest(suite, {"Task.tla": {"context": ["one/Model.tla", "two/Model.tla"]}})

    with pytest.raises(ManifestError, match="duplicate module basename 'Model.tla'"):
        load_proof_from_scratch_manifest(suite)


def test_filename_must_match_declared_module_name(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "Task.tla", declared_name="Different")
    _write_manifest(suite, {"Task.tla": {"context": []}})

    with pytest.raises(ManifestError, match="filename/module mismatch"):
        load_proof_from_scratch_manifest(suite)


def test_in_suite_symlink_cannot_hide_filename_module_mismatch(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_module(suite, "Task.tla")
    real_module = _write_module(suite, "real/Model.tla")
    alias = suite / "alias/Alias.tla"
    alias.parent.mkdir()
    alias.symlink_to(real_module)
    _write_manifest(suite, {"Task.tla": {"context": ["alias/Alias.tla"]}})

    with pytest.raises(ManifestError, match="filename/module mismatch.*Alias"):
        load_proof_from_scratch_manifest(suite)


def test_every_file_must_have_a_module_header(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    suite.mkdir()
    (suite / "Task.tla").write_text("THEOREM Target == TRUE\n", encoding="utf-8")
    _write_manifest(suite, {"Task.tla": {"context": []}})

    with pytest.raises(ManifestError, match="has no module header"):
        load_proof_from_scratch_manifest(suite)


def test_parse_editable_regions_preserves_fixed_and_editable_bytes():
    source = _canonical_source()

    regions = parse_editable_regions(source)

    assert regions.fixed_prefix == (f"---- MODULE Task ----\nEXTENDS TaskDefs\n\n{BEGIN_AGENT_HELPERS}\n")
    assert regions.helpers == "Helper == TRUE\n"
    assert regions.fixed_middle == (f"{END_AGENT_HELPERS}\n\nTHEOREM Target == TRUE\n{BEGIN_AGENT_PROOF}\n")
    assert regions.proof == "PROOF OBVIOUS\n"
    assert regions.fixed_suffix == f"{END_AGENT_PROOF}\n====\n"
    assert regions.render() == source

    edited = regions.render(helpers="Fresh == 1\n", proof="PROOF BY Fresh\n")
    edited_regions = parse_editable_regions(edited)
    assert edited_regions.helpers == "Fresh == 1\n"
    assert edited_regions.proof == "PROOF BY Fresh\n"
    assert edited_regions.fixed_segments == regions.fixed_segments


def test_parse_editable_regions_preserves_crlf_marker_bytes():
    source = _canonical_source("\r\n")

    regions = parse_editable_regions(source)

    assert regions.helpers == "Helper == TRUE\r\n"
    assert regions.proof == "PROOF OBVIOUS\r\n"
    assert regions.fixed_prefix.endswith(f"{BEGIN_AGENT_HELPERS}\r\n")
    assert regions.fixed_middle.endswith(f"{BEGIN_AGENT_PROOF}\r\n")
    assert regions.fixed_suffix.startswith(f"{END_AGENT_PROOF}\r\n")
    assert regions.render() == source


@pytest.mark.parametrize("marker", [BEGIN_AGENT_HELPERS, END_AGENT_HELPERS, BEGIN_AGENT_PROOF, END_AGENT_PROOF])
def test_missing_marker_is_rejected(marker):
    source = _canonical_source().replace(f"{marker}\n", "", 1)

    with pytest.raises(EditableRegionError, match="exactly once, found 0"):
        parse_editable_regions(source)


@pytest.mark.parametrize("suffix", [" ", " extra"])
def test_marker_lines_must_be_exact(suffix):
    source = _canonical_source().replace(BEGIN_AGENT_HELPERS, BEGIN_AGENT_HELPERS + suffix, 1)

    with pytest.raises(EditableRegionError, match="exactly once, found 0"):
        parse_editable_regions(source)


def test_duplicate_marker_is_rejected():
    source = _canonical_source().replace(
        f"{BEGIN_AGENT_HELPERS}\n",
        f"{BEGIN_AGENT_HELPERS}\n{BEGIN_AGENT_HELPERS}\n",
        1,
    )

    with pytest.raises(EditableRegionError, match="exactly once, found 2"):
        parse_editable_regions(source)


def test_reordered_markers_are_rejected():
    source = "\n".join(
        (
            "---- MODULE Task ----",
            END_AGENT_HELPERS,
            BEGIN_AGENT_HELPERS,
            BEGIN_AGENT_PROOF,
            END_AGENT_PROOF,
            "====",
            "",
        )
    )

    with pytest.raises(EditableRegionError, match="not in the required order"):
        parse_editable_regions(source)
