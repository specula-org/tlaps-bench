import json
import sys
from types import SimpleNamespace

import pytest

from common import validate
from common.proof_completion_contract import BEGIN_AGENT_PROOF, END_AGENT_PROOF
from common.task_contract import TaskContractError
from common.validate import _validation_work_item, discover_benchmarks, validation_dependencies, validation_exit_code


def _write_module(path, body):
    path.write_text(f"---- MODULE {path.stem} ----\n{body}\n====\n")


def test_discovery_and_dependencies_use_runner_rules(tmp_path):
    benchmark_dir = tmp_path / "benchmark" / "proof-completion"
    example_dir = benchmark_dir / "Example"
    example_dir.mkdir(parents=True)

    dependency = example_dir / "Shared_proof.tla"
    task = example_dir / "Shared_proof_Goal.tla"
    other_task = example_dir / "Other_Goal.tla"
    _write_module(dependency, "Value == TRUE")
    _write_module(
        task,
        f"EXTENDS Shared_proof\nTHEOREM Goal == Value\n{BEGIN_AGENT_PROOF}\nPROOF OBVIOUS\n{END_AGENT_PROOF}",
    )
    _write_module(
        other_task,
        f"THEOREM Other == TRUE\n{BEGIN_AGENT_PROOF}\nPROOF OBVIOUS\n{END_AGENT_PROOF}",
    )
    (benchmark_dir / "manifest.json").write_text(
        json.dumps(
            {
                "Example/Shared_proof_Goal.tla": {
                    "spec_id": "Example.tla",
                    "context": ["Example/Shared_proof.tla"],
                    "reference_proof_steps": 0,
                },
                "Example/Other_Goal.tla": {
                    "spec_id": "Example.tla",
                    "context": [],
                    "reference_proof_steps": 0,
                },
            }
        )
    )

    assert discover_benchmarks(benchmark_dir=str(benchmark_dir)) == [str(other_task), str(task)]
    assert discover_benchmarks("Shared_proof_Goal", str(benchmark_dir)) == [str(task)]
    assert validation_dependencies(str(task), str(benchmark_dir)) == [str(dependency)]


def test_validation_exit_code_succeeds_only_when_every_task_passes():
    assert validation_exit_code([SimpleNamespace(status="PASS"), SimpleNamespace(status="PASS")]) == 0


@pytest.mark.parametrize("status", ["FAIL", "ERROR", "OMITTED", "NO_PROOF"])
def test_validation_exit_code_fails_for_any_non_pass_status(status):
    assert validation_exit_code([SimpleNamespace(status="PASS"), SimpleNamespace(status=status)]) == 1


def test_validation_work_item_keeps_image_for_initial_and_rerun_pools():
    item = _validation_work_item(
        "/bench/Example.tla",
        ["/bench/Model.tla"],
        [("Example", "/source/Example.tla")],
        "/opt/tlapm/bin/tlapm",
        "/opt/tlapm/lib",
        120,
        True,
        "tlaps-bench-base:immutable",
    )

    assert item[1] == ["/bench/Model.tla"]
    assert item[-2:] == (True, "tlaps-bench-base:immutable")


def test_validation_cli_reports_contract_errors_without_traceback(monkeypatch, capsys):
    class InvalidMode:
        def get_benchmark_files(self, _filter):
            raise TaskContractError("marked proof-completion suite is missing its manifest")

    monkeypatch.setattr(validate, "_proof_completion_mode", InvalidMode)
    monkeypatch.setattr(sys, "argv", ["tlaps-bench validate"])

    with pytest.raises(SystemExit) as exc_info:
        validate.main()

    assert exc_info.value.code == 2
    stderr = capsys.readouterr().err
    assert "marked proof-completion suite is missing its manifest" in stderr
    assert "Traceback" not in stderr


def _validation_fixture(tmp_path, monkeypatch):
    benchmark = tmp_path / "benchmark" / "Example" / "Task_Goal.tla"
    source = tmp_path / "source" / "Example" / "Task.tla"
    benchmark.parent.mkdir(parents=True)
    source.parent.mkdir(parents=True)
    _write_module(benchmark, "THEOREM Goal == TRUE\nPROOF OBVIOUS")
    _write_module(source, "THEOREM Goal == TRUE\nPROOF BY TRUE")
    monkeypatch.setattr(validate, "SOURCE_ROOT", str(tmp_path / "source"))
    item = _validation_work_item(
        str(benchmark),
        [],
        [("Task", str(source))],
        "/bin/true",
        str(tmp_path),
        120,
        False,
        "unused",
    )
    return item


def test_sany_invalid_reference_is_fail_and_batch_can_continue(tmp_path, monkeypatch):
    item = _validation_fixture(tmp_path, monkeypatch)
    monkeypatch.setattr(validate, "run_sany", lambda *_args: ("invalid", "duplicate field"))
    monkeypatch.setattr(
        validate,
        "run_tlapm",
        lambda *_args: pytest.fail("SANY-invalid reference must stop before TLAPM"),
    )

    result = validate.validate_single_benchmark(item)

    assert result.status == "FAIL"
    assert result.sany_status == "invalid"
    assert result.error == ""


def test_sany_unavailable_reference_is_error(tmp_path, monkeypatch):
    item = _validation_fixture(tmp_path, monkeypatch)
    monkeypatch.setattr(validate, "run_sany", lambda *_args: ("unavailable", "tool missing"))
    monkeypatch.setattr(
        validate,
        "run_tlapm",
        lambda *_args: pytest.fail("SANY-unavailable reference must stop before TLAPM"),
    )

    result = validate.validate_single_benchmark(item)

    assert result.status == "ERROR"
    assert result.sany_status == "unavailable"
    assert "tool missing" in result.error
