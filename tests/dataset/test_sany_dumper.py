"""Regression tests for the SANY semantic dependency dump."""

import importlib
import subprocess

from dataset.proof_from_scratch.generate import compute_reachable, dump_sany
from tlacore.sany.dump import SanyStatus, run_normalized, run_raw

sany_dump = importlib.import_module("tlacore.sany.dump")


def test_named_operator_argument_is_reachable(tmp_path):
    source = tmp_path / "OperatorArgument.tla"
    source.write_text(
        """------------------------- MODULE OperatorArgument -------------------------
EXTENDS Sequences

CONSTANT Items

Keep(item) == TRUE
Filtered == SelectSeq(Items, Keep)

THEOREM Goal == Filtered = Filtered
PROOF OBVIOUS
=============================================================================
"""
    )

    dump = dump_sany(str(source))
    filtered = next(op for op in dump["operators"] if op["name"] == "Filtered")
    target = next(theorem for theorem in dump["theorems"] if theorem["name"] == "Goal")

    assert filtered["references"] == ["Keep"]
    assert {"Filtered", "Keep"} <= compute_reachable(dump, target)


def test_duplicate_record_fields_are_rejected_by_sany(tmp_path):
    source = tmp_path / "Foo.tla"
    source.write_text(
        """---- MODULE Foo -----
THEOREM Eq    == [a |-> 1, a |-> 2] = [a |-> 1, a |-> 3] OBVIOUS
THEOREM False == ASSUME NEW r, r = [a |-> 1, a |-> 2] PROVE FALSE OBVIOUS
=====
"""
    )

    run = run_normalized(str(source))

    assert run.status is SanyStatus.INVALID
    assert run.returncode == 3
    assert "Non-unique fields in constructor" in run.stderr


def test_exit_three_is_invalid_without_matching_diagnostic_text(monkeypatch, tmp_path):
    source = tmp_path / "Foo.tla"
    source.write_text("---- MODULE Foo ----\n====\n")
    stderr = "x" * 800 + " diagnostic without a known keyword"
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 3, stdout="", stderr=stderr),
    )

    run = run_raw(str(source))

    assert run.status is SanyStatus.INVALID
    assert stderr in run.detail


def test_missing_sany_runner_is_unavailable(monkeypatch, tmp_path):
    source = tmp_path / "Foo.tla"
    source.write_text("---- MODULE Foo ----\n====\n")

    def missing(*_args, **_kwargs):
        raise FileNotFoundError("run.sh missing")

    monkeypatch.setattr(subprocess, "run", missing)

    run = run_raw(str(source))

    assert run.status is SanyStatus.UNAVAILABLE
    assert "run.sh missing" in run.detail


def test_sany_timeout_is_unavailable_without_retry(monkeypatch, tmp_path):
    source = tmp_path / "Foo.tla"
    source.write_text("---- MODULE Foo ----\n====\n")
    calls = 0

    def timeout(*_args, **_kwargs):
        nonlocal calls
        calls += 1
        raise subprocess.TimeoutExpired(["sany"], 120)

    monkeypatch.setattr(subprocess, "run", timeout)

    run = run_raw(str(source), timeout=120)

    assert run.status is SanyStatus.UNAVAILABLE
    assert calls == 1


def test_normalized_staging_directory_failure_is_unavailable(monkeypatch, tmp_path):
    source = tmp_path / "solution.tla"
    source.write_text("---- MODULE Foo ----\n====\n")

    def fail(*_args, **_kwargs):
        raise OSError("disk full")

    monkeypatch.setattr(sany_dump.tempfile, "mkdtemp", fail)

    run = run_normalized(str(source))

    assert run.status is SanyStatus.UNAVAILABLE
    assert "SANY staging failed" in run.detail
    assert "disk full" in run.detail


def test_normalized_copy_failure_is_unavailable(monkeypatch, tmp_path):
    source = tmp_path / "solution.tla"
    source.write_text("---- MODULE Foo ----\n====\n")

    def fail(*_args, **_kwargs):
        raise OSError("copy failed")

    monkeypatch.setattr(sany_dump.shutil, "copy2", fail)

    run = run_normalized(str(source))

    assert run.status is SanyStatus.UNAVAILABLE
    assert "SANY staging failed" in run.detail
    assert "copy failed" in run.detail
