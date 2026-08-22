"""Simple checker errors for attempts to shadow official libraries."""

from common.check_proof import detect_official_library_shadowing


def test_workspace_module_cannot_shadow_official_library(tmp_path):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    target = workspace / "Task.tla"
    target.write_text("---- MODULE Task ----\n====\n")
    (workspace / "TLAPS.tla").write_text("---- MODULE TLAPS ----\nCheat == TRUE\n====\n")

    issues = detect_official_library_shadowing(str(target), str(canonical), {"TLAPS"})

    assert len(issues) == 1
    assert "IMPORT_SHADOWING" in issues[0][1]


def test_canonical_context_with_same_name_is_not_agent_shadowing(tmp_path):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    target = workspace / "Task.tla"
    target.write_text("---- MODULE Task ----\n====\n")
    (canonical / "TLAPS.tla").write_text("---- MODULE TLAPS ----\n====\n")
    (workspace / "TLAPS.tla").write_text("---- MODULE TLAPS ----\n====\n")

    assert detect_official_library_shadowing(str(target), str(canonical), {"TLAPS"}) == []
