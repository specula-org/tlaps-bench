"""Canonical proof-from-scratch staging and fixed-region integrity."""

from __future__ import annotations

import os
import sys

import pytest

from common import check_proof
from common.proof_from_scratch_contract import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
)
from tlacheck.issue import Issue, Severity
from tlacheck.verdict import Result, Verdict
from tlacore.sany.dump import SanyRun, SanyStatus


def _sany_run(status: str, detail: str = "") -> SanyRun:
    return SanyRun(SanyStatus(status), ("sany",), 0 if status == "valid" else None, "", "", detail)


def _task(*, helper="Helper == TRUE", proof="PROOF OBVIOUS", statement="THEOREM Target == TRUE"):
    return "\n".join(
        (
            "---- MODULE Task ----",
            "EXTENDS Model",
            "",
            BEGIN_AGENT_HELPERS,
            helper,
            END_AGENT_HELPERS,
            "",
            statement,
            BEGIN_AGENT_PROOF,
            proof,
            END_AGENT_PROOF,
            "====",
            "",
        )
    )


def _completion_task(*, proof="PROOF OBVIOUS", statement="THEOREM Target == TRUE", suffix="===="):
    return "\n".join(
        (
            "---- MODULE Task ----",
            "EXTENDS Model",
            "",
            statement,
            BEGIN_AGENT_PROOF,
            proof,
            END_AGENT_PROOF,
            suffix,
            "",
        )
    )


def test_canonical_replay_stages_submitted_target_with_only_canonical_context(tmp_path):
    workspace = tmp_path / "workspace"
    canonical = tmp_path / "canonical"
    staged = tmp_path / "staged"
    workspace.mkdir()
    canonical.mkdir()
    staged.mkdir()

    submitted = _task(proof="PROOF BY TRUE")
    (workspace / "Task.tla").write_text(submitted)
    (workspace / "Model.tla").write_text("TAMPERED MODEL")
    (workspace / "AgentOnly.tla").write_text("AGENT MODULE")
    (canonical / "Task.tla").write_text(_task())
    (canonical / "Model.tla").write_text("CANONICAL MODEL")
    (canonical / "Defs.tla").write_text("CANONICAL DEFS")

    staged_target = check_proof.stage_verification_files(
        str(workspace / "Task.tla"),
        str(staged),
        benchmark_dir=str(canonical),
        require_canonical=True,
    )

    assert (staged / "Task.tla").read_text() == submitted
    assert (staged / "Model.tla").read_text() == "CANONICAL MODEL"
    assert (staged / "Defs.tla").read_text() == "CANONICAL DEFS"
    assert not (staged / "AgentOnly.tla").exists()
    assert staged_target == str(staged / "Task.tla")


def test_noncanonical_staging_preserves_existing_workspace_behavior(tmp_path):
    workspace = tmp_path / "workspace"
    canonical = tmp_path / "canonical"
    staged = tmp_path / "staged"
    workspace.mkdir()
    canonical.mkdir()
    staged.mkdir()
    (workspace / "Task.tla").write_text("SUBMITTED")
    (workspace / "Model.tla").write_text("WORKSPACE MODEL")
    (canonical / "Task.tla").write_text("CANONICAL")
    (canonical / "Model.tla").write_text("CANONICAL MODEL")

    check_proof.stage_verification_files(
        str(workspace / "Task.tla"),
        str(staged),
        benchmark_dir=str(canonical),
        require_canonical=False,
    )

    assert (staged / "Task.tla").read_text() == "SUBMITTED"
    assert (staged / "Model.tla").read_text() == "WORKSPACE MODEL"


def test_canonical_staging_fails_without_canonical_directory(tmp_path):
    target = tmp_path / "Task.tla"
    staged = tmp_path / "staged"
    target.write_text("SUBMITTED")
    staged.mkdir()

    with pytest.raises(ValueError, match="canonical replay required"):
        check_proof.stage_verification_files(str(target), str(staged), require_canonical=True)


def test_helper_and_proof_region_changes_preserve_fixed_scaffold(tmp_path):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    (canonical / "Task.tla").write_text(_task())
    target.write_text(_task(helper="Fresh == 1", proof="PROOF BY TRUE"))

    assert check_proof.check_editable_region_integrity(str(target), str(canonical)) == []


def test_proof_only_region_change_preserves_fixed_scaffold(tmp_path):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    (canonical / "Task.tla").write_text(_completion_task())
    target.write_text(_completion_task(proof="PROOF BY TRUE"))

    assert check_proof.check_editable_region_integrity(str(target), str(canonical), proof_only=True) == []


@pytest.mark.parametrize(
    "submitted",
    [
        _completion_task(statement="THEOREM Target == FALSE"),
        _completion_task(suffix="Changed == TRUE\n===="),
        _completion_task().replace(BEGIN_AGENT_PROOF, r"\* CHANGED AGENT PROOF"),
    ],
)
def test_proof_only_fixed_text_or_marker_change_is_rejected(tmp_path, submitted):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    (canonical / "Task.tla").write_text(_completion_task())
    target.write_text(submitted)

    issues = check_proof.check_editable_region_integrity(str(target), str(canonical), proof_only=True)

    assert issues[0][2] == "SCAFFOLD_MODIFIED"


def test_proof_only_extra_eof_newlines_are_ignored(tmp_path):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    (canonical / "Task.tla").write_text(_completion_task())
    target.write_text(_completion_task() + "\r\n\n")

    assert check_proof.check_editable_region_integrity(str(target), str(canonical), proof_only=True) == []


def test_fixed_scaffold_change_is_rejected(tmp_path):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    (canonical / "Task.tla").write_text(_task())
    target.write_text(_task(statement="THEOREM Target == FALSE"))

    issues = check_proof.check_editable_region_integrity(str(target), str(canonical))

    assert issues == [(0, "fixed task scaffold outside editable regions was modified", "SCAFFOLD_MODIFIED")]


@pytest.mark.parametrize(
    "submitted",
    [
        _task().replace("\n", "\r\n"),
        _task().removesuffix("\n"),
    ],
)
def test_newline_only_scaffold_change_is_a_non_cheat_boundary_failure(tmp_path, submitted):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    (canonical / "Task.tla").write_bytes(_task().encode())
    target.write_bytes(submitted.encode())

    issues = check_proof.check_editable_region_integrity(str(target), str(canonical))

    assert issues == [
        (
            0,
            "fixed task scaffold differs only in line endings or the final newline",
            "SCAFFOLD_FORMAT_MODIFIED",
        )
    ]


def test_marker_change_is_rejected(tmp_path):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    (canonical / "Task.tla").write_text(_task())
    target.write_text(_task().replace(BEGIN_AGENT_PROOF, r"\* AGENT PROOF", 1))

    issues = check_proof.check_editable_region_integrity(str(target), str(canonical))

    assert issues[0][2] == "SCAFFOLD_MODIFIED"
    assert "markers were modified" in issues[0][1]


def test_invalid_canonical_markers_are_infrastructure_error(tmp_path):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    (canonical / "Task.tla").write_text(_task().replace(END_AGENT_HELPERS, "", 1))
    target.write_text(_task())

    with pytest.raises(RuntimeError, match="canonical proof-from-scratch task has invalid editable regions"):
        check_proof.check_editable_region_integrity(str(target), str(canonical))


def test_canonical_replay_requirement_can_come_from_runner_environment(monkeypatch):
    monkeypatch.delenv("TLAPS_CANONICAL_REPLAY_REQUIRED", raising=False)
    assert not check_proof.canonical_replay_required(False)
    monkeypatch.setenv("TLAPS_CANONICAL_REPLAY_REQUIRED", "1")
    assert check_proof.canonical_replay_required(False)
    assert check_proof.canonical_replay_required(True)


def test_sany_only_does_not_require_canonical_replay_for_marked_completion(tmp_path, monkeypatch, capsys):
    target = tmp_path / "Task.tla"
    target.write_text(_completion_task())
    (tmp_path / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    monkeypatch.delenv("TLAPS_BENCHMARK_DIR", raising=False)
    monkeypatch.setenv("TLAPS_CANONICAL_REPLAY_REQUIRED", "1")
    monkeypatch.setattr(
        check_proof,
        "stage_verification_files",
        lambda *_args, **_kwargs: pytest.fail("--sany-only must not stage canonical files"),
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-completion",
            "--no-container",
            "--sany-only",
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 0
    assert "SANY-STATUS: valid" in capsys.readouterr().out


def test_full_marked_check_requires_canonical_directory(tmp_path, monkeypatch, capsys):
    target = tmp_path / "Task.tla"
    target.write_text(_completion_task())
    monkeypatch.delenv("TLAPS_BENCHMARK_DIR", raising=False)
    monkeypatch.delenv("TLAPS_CANONICAL_REPLAY_REQUIRED", raising=False)
    monkeypatch.setattr(
        sys,
        "argv",
        ["check_proof", str(target), "--mode", "proof-completion", "--no-container", "--no-git-track"],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 3
    assert "canonical replay required" in capsys.readouterr().out


def test_full_marked_check_rejects_self_canonical_target(tmp_path, monkeypatch, capsys):
    target = tmp_path / "Task.tla"
    target.write_text(_completion_task())
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-completion",
            "--no-container",
            "--no-git-track",
            "--benchmark-dir",
            str(tmp_path),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 3
    assert "canonical benchmark target must be independent" in capsys.readouterr().out


def test_full_unmarked_check_rejects_explicit_self_canonical_target(tmp_path, monkeypatch, capsys):
    target = tmp_path / "Task.tla"
    target.write_text("---- MODULE Task ----\nTHEOREM Target == TRUE\nPROOF BY TRUE\n====\n")
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-completion",
            "--no-container",
            "--no-git-track",
            "--benchmark-dir",
            str(tmp_path),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 3
    assert "canonical benchmark target must be independent" in capsys.readouterr().out


def test_full_marked_check_rejects_symlinked_canonical_target(tmp_path, monkeypatch, capsys):
    workspace = tmp_path / "workspace"
    canonical = tmp_path / "canonical"
    workspace.mkdir()
    canonical.mkdir()
    target = workspace / "Task.tla"
    target.write_text(_completion_task())
    (canonical / "Task.tla").symlink_to(target)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-completion",
            "--no-container",
            "--no-git-track",
            "--benchmark-dir",
            str(canonical),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 3
    assert "canonical benchmark target must be independent" in capsys.readouterr().out


def test_independent_canonical_check_rejects_hardlink(tmp_path):
    workspace = tmp_path / "workspace"
    canonical = tmp_path / "canonical"
    workspace.mkdir()
    canonical.mkdir()
    target = workspace / "Task.tla"
    target.write_text(_completion_task())
    os.link(target, canonical / "Task.tla")

    with pytest.raises(RuntimeError, match="canonical benchmark target must be independent"):
        check_proof.require_independent_canonical_target(str(target), str(canonical))


def test_independent_canonical_check_ignores_missing_target(tmp_path):
    submitted = tmp_path / "Task.tla"
    canonical = tmp_path / "canonical"
    submitted.write_text(_completion_task())
    canonical.mkdir()

    check_proof.require_independent_canonical_target(str(submitted), str(canonical))


def test_direct_marked_completion_check_rejects_fixed_scaffold_change(tmp_path, monkeypatch):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    (canonical / "Task.tla").write_text(_completion_task())
    (canonical / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    target = workspace / "Task.tla"
    target.write_text(_completion_task(statement="THEOREM Target == TRUE /\\ TRUE"))
    (workspace / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    output = tmp_path / "check.result"

    monkeypatch.delenv("TLAPS_CANONICAL_REPLAY_REQUIRED", raising=False)
    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: _sany_run("valid"))
    monkeypatch.setattr(
        check_proof,
        "run_killgroup",
        lambda *_args, **_kwargs: pytest.fail("scaffold failure must stop before TLAPM"),
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-completion",
            "--no-container",
            "--no-git-track",
            "--benchmark-dir",
            str(canonical),
            "--tlapm",
            "/bin/true",
            "--tlapm-lib",
            str(tmp_path),
            "--output",
            str(output),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 1
    assert "fixed task scaffold outside editable regions was modified" in output.read_text()


def test_legacy_canonical_target_cannot_be_upgraded_by_submitted_markers(tmp_path):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = tmp_path / "Task.tla"
    baseline = "\n".join(
        (
            "---- MODULE Task ----",
            "Value == TRUE",
            "THEOREM Target == Value",
            "PROOF OBVIOUS",
            "====",
            "",
        )
    )
    (canonical / "Task.tla").write_text(baseline)
    target.write_text(
        baseline.replace("Value == TRUE", "Value == FALSE").replace(
            "PROOF OBVIOUS",
            f"{BEGIN_AGENT_PROOF}\nPROOF OBVIOUS\n{END_AGENT_PROOF}",
        )
    )

    marked = check_proof.task_has_proof_region_markers(str(target), str(canonical))
    issues = check_proof.check_cheating(
        str(target),
        strict_preamble=not marked,
        benchmark_dir=str(canonical),
    )

    assert not marked
    assert "PREAMBLE_MODIFIED" in {issue[2] for issue in issues}


def test_legacy_canonical_sibling_tasks_are_not_required_dependencies(tmp_path):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    baseline = "\n".join(
        (
            "---- MODULE Task ----",
            "THEOREM Target == TRUE",
            "PROOF OBVIOUS",
            "====",
            "",
        )
    )
    (canonical / "Task.tla").write_text(baseline)
    (canonical / "Unrelated_OtherGoal.tla").write_text(
        "---- MODULE Unrelated_OtherGoal ----\nTHEOREM Other == TRUE\nPROOF OBVIOUS\n====\n"
    )
    target = workspace / "Task.tla"
    target.write_text(baseline)

    issues = check_proof.check_cheating(
        str(target),
        strict_preamble=True,
        benchmark_dir=str(canonical),
    )

    assert "DEPENDENCY_MODIFIED" not in {issue[2] for issue in issues}


def test_legacy_workspace_dependency_is_compared_to_canonical_baseline(tmp_path):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    baseline = "---- MODULE Task ----\nTHEOREM Target == TRUE\nPROOF OBVIOUS\n====\n"
    (canonical / "Task.tla").write_text(baseline)
    (canonical / "Model.tla").write_text("---- MODULE Model ----\nValue == TRUE\n====\n")
    target = workspace / "Task.tla"
    target.write_text(baseline)
    (workspace / "Model.tla").write_text("---- MODULE Model ----\nValue == FALSE\n====\n")

    issues = check_proof.check_cheating(
        str(target),
        strict_preamble=True,
        benchmark_dir=str(canonical),
    )

    assert any(issue[2] == "DEPENDENCY_MODIFIED" and "Model.tla" in issue[1] for issue in issues)


@pytest.mark.parametrize("dependency_state", ["missing", "invalid-utf8"])
def test_uncomparable_canonical_dependency_is_rejected(tmp_path, dependency_state):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    (canonical / "Task.tla").write_text(_completion_task())
    (canonical / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    target = workspace / "Task.tla"
    target.write_text(_completion_task())
    if dependency_state == "invalid-utf8":
        (workspace / "Model.tla").write_bytes(b"\xff")

    issues = check_proof.check_cheating(
        str(target),
        strict_preamble=False,
        benchmark_dir=str(canonical),
        require_complete_context=True,
    )

    assert "DEPENDENCY_MODIFIED" in {issue[2] for issue in issues}


def test_fixed_scaffold_failure_stops_before_tlapm(tmp_path, monkeypatch):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    (canonical / "Task.tla").write_text(_task())
    (canonical / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    target = workspace / "Task.tla"
    target.write_text(_task(statement="THEOREM Target == FALSE"))
    (workspace / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    output = tmp_path / "check.result"

    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: _sany_run("valid"))
    monkeypatch.setattr(
        check_proof,
        "run_killgroup",
        lambda *_args, **_kwargs: pytest.fail("boundary failure must stop before TLAPM"),
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-from-scratch",
            "--no-container",
            "--no-git-track",
            "--benchmark-dir",
            str(canonical),
            "--tlapm",
            "/bin/true",
            "--tlapm-lib",
            str(tmp_path),
            "--output",
            str(output),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 1
    assert "fixed task scaffold outside editable regions was modified" in output.read_text()


def test_newline_only_scaffold_failure_is_not_reported_as_cheating(tmp_path, monkeypatch):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    (canonical / "Task.tla").write_bytes(_task().encode())
    (canonical / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    target = workspace / "Task.tla"
    target.write_bytes(_task().replace("\n", "\r\n").encode())
    (workspace / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    output = tmp_path / "check.result"

    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: _sany_run("valid"))
    monkeypatch.setattr(
        check_proof,
        "run_killgroup",
        lambda *_args, **_kwargs: pytest.fail("boundary failure must stop before TLAPM"),
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-from-scratch",
            "--no-container",
            "--no-git-track",
            "--canonical-replay-required",
            "--benchmark-dir",
            str(canonical),
            "--tlapm",
            "/bin/true",
            "--tlapm-lib",
            str(tmp_path),
            "--output",
            str(output),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    result = output.read_text()
    assert exc_info.value.code == 1
    assert "scaffold_format_unchanged" in result
    assert "CHEAT-DETECTED" not in result


def test_required_canonical_sany_failure_is_infrastructure_error(tmp_path, monkeypatch):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    (canonical / "Task.tla").write_text(_task())
    (canonical / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    target = workspace / "Task.tla"
    target.write_text(_task(proof="PROOF BY TRUE"))
    (workspace / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    output = tmp_path / "check.result"

    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: _sany_run("unavailable", "missing tool"))
    monkeypatch.setattr(
        check_proof,
        "run_killgroup",
        lambda *_args, **_kwargs: pytest.fail("missing canonical SANY must stop before TLAPM"),
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-from-scratch",
            "--no-container",
            "--no-git-track",
            "--canonical-replay-required",
            "--benchmark-dir",
            str(canonical),
            "--tlapm",
            "/bin/true",
            "--tlapm-lib",
            str(tmp_path),
            "--output",
            str(output),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 3
    assert "SANY validation unavailable" in output.read_text()
    assert "status: unavailable" in (tmp_path / "sany.log").read_text()
    assert "missing tool" in (tmp_path / "sany.log").read_text()


def test_required_canonical_semantic_failure_is_infrastructure_error(tmp_path, monkeypatch):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    (canonical / "Task.tla").write_text(_task())
    (canonical / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    target = workspace / "Task.tla"
    target.write_text(_task(proof="PROOF BY TRUE"))
    (workspace / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    output = tmp_path / "check.result"

    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: _sany_run("valid"))
    monkeypatch.setattr(
        check_proof,
        "run_tlacheck_engine",
        lambda *_args, **_kwargs: ([], "engine crashed", None),
    )

    def summary_only(command, *_args, **_kwargs):
        if "--summary" in command:
            return "", "", 0
        pytest.fail("missing canonical semantic validation must stop before full TLAPM")

    monkeypatch.setattr(check_proof, "run_killgroup", summary_only)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-from-scratch",
            "--no-container",
            "--no-git-track",
            "--canonical-replay-required",
            "--benchmark-dir",
            str(canonical),
            "--tlapm",
            "/bin/true",
            "--tlapm-lib",
            str(tmp_path),
            "--output",
            str(output),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 3
    assert "semantic validation unavailable: engine crashed" in output.read_text()


def test_helper_policy_failure_stops_before_full_tlapm(tmp_path, monkeypatch):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    (canonical / "Task.tla").write_text(_task(helper=""))
    (canonical / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    target = workspace / "Task.tla"
    target.write_text(_task(helper="CONSTANT C", proof="PROOF BY TRUE"))
    (workspace / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    output = tmp_path / "check.result"

    issue = Issue(
        "HELPER_REGION_VIOLATION",
        Severity.CHEATING,
        "CONSTANT declarations are not allowed in the helper region",
    )
    engine_result = Result(Verdict.CHEATING, [issue])
    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: _sany_run("valid"))
    monkeypatch.setattr(
        check_proof,
        "run_tlacheck_engine",
        lambda *_args, **_kwargs: ([str(issue)], "", engine_result),
    )
    calls = []

    def fake_run(command, *_args, **_kwargs):
        calls.append(command)
        if "--summary" in command:
            return "", "", 0
        pytest.fail("helper policy failure must stop before the full TLAPM run")

    monkeypatch.setattr(check_proof, "run_killgroup", fake_run)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-from-scratch",
            "--no-container",
            "--no-git-track",
            "--canonical-replay-required",
            "--benchmark-dir",
            str(canonical),
            "--tlapm",
            "/bin/true",
            "--tlapm-lib",
            str(tmp_path),
            "--output",
            str(output),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    result = output.read_text()
    assert exc_info.value.code == 1
    assert len(calls) == 1
    assert "--summary" in calls[0]
    assert "editable_regions_valid" in result
    assert "CHEAT-DETECTED: editable_regions_valid" in result


def test_proof_only_declaration_policy_stops_before_full_tlapm(tmp_path, monkeypatch):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    (canonical / "Task.tla").write_text(_completion_task())
    (canonical / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    target = workspace / "Task.tla"
    target.write_text(_completion_task(proof="PROOF BY TRUE\nLate == TRUE"))
    (workspace / "Model.tla").write_text("---- MODULE Model ----\n====\n")
    output = tmp_path / "check.result"

    issue = Issue(
        "HELPER_REGION_VIOLATION",
        Severity.CHEATING,
        "module-level operator declarations are not allowed in the proof region",
    )
    engine_result = Result(Verdict.CHEATING, [issue])
    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: _sany_run("valid"))
    monkeypatch.setattr(
        check_proof,
        "run_tlacheck_engine",
        lambda *_args, **_kwargs: ([str(issue)], "", engine_result),
    )
    calls = []

    def fake_run(command, *_args, **_kwargs):
        calls.append(command)
        if "--summary" in command:
            return "", "", 0
        pytest.fail("proof-region policy failure must stop before the full TLAPM run")

    monkeypatch.setattr(check_proof, "run_killgroup", fake_run)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "check_proof",
            str(target),
            "--mode",
            "proof-completion",
            "--no-container",
            "--no-git-track",
            "--canonical-replay-required",
            "--benchmark-dir",
            str(canonical),
            "--tlapm",
            "/bin/true",
            "--tlapm-lib",
            str(tmp_path),
            "--output",
            str(output),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    result = output.read_text()
    assert exc_info.value.code == 1
    assert len(calls) == 1
    assert "--summary" in calls[0]
    assert "CHEAT-DETECTED: editable_regions_valid" in result
