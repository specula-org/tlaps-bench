from types import SimpleNamespace

import pytest

from common.validate import discover_benchmarks, validation_dependencies, validation_exit_code


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
    _write_module(task, "EXTENDS Shared_proof\nTHEOREM Goal == Value\nPROOF OBVIOUS")
    _write_module(other_task, "THEOREM Other == TRUE\nPROOF OBVIOUS")

    assert discover_benchmarks(benchmark_dir=str(benchmark_dir)) == [str(other_task), str(task)]
    assert discover_benchmarks("Shared_proof_Goal", str(benchmark_dir)) == [str(task)]
    assert validation_dependencies(str(task), str(benchmark_dir)) == [str(dependency)]


def test_validation_exit_code_succeeds_only_when_every_task_passes():
    assert validation_exit_code([SimpleNamespace(status="PASS"), SimpleNamespace(status="PASS")]) == 0


@pytest.mark.parametrize("status", ["FAIL", "ERROR", "OMITTED", "NO_PROOF"])
def test_validation_exit_code_fails_for_any_non_pass_status(status):
    assert validation_exit_code([SimpleNamespace(status="PASS"), SimpleNamespace(status=status)]) == 1
