"""The standalone SANY parse gate is mandatory in every checker mode."""

import sys

import pytest

from common import check_proof
from tlacore.sany.dump import SanyRun, SanyStatus

DUPLICATE_RECORD = """---- MODULE Foo -----
THEOREM Eq    == [a |-> 1, a |-> 2] = [a |-> 1, a |-> 3] OBVIOUS
THEOREM False == ASSUME NEW r, r = [a |-> 1, a |-> 2] PROVE FALSE OBVIOUS
=====
"""


def _argv(source, output, mode, *extra):
    return [
        "check_proof",
        str(source),
        "--mode",
        mode,
        "--no-container",
        "--no-git-track",
        "--tlapm",
        "/bin/true",
        "--tlapm-lib",
        str(source.parent),
        "--output",
        str(output),
        *extra,
    ]


@pytest.mark.parametrize("mode", ["proof-completion", "proof-from-scratch"])
def test_tlapm_accepted_duplicate_record_module_fails_every_mode(tmp_path, monkeypatch, mode):
    source = tmp_path / "Foo.tla"
    source.write_text(DUPLICATE_RECORD)
    output = tmp_path / "check.result"
    monkeypatch.setattr(
        check_proof,
        "run_killgroup",
        lambda *_args, **_kwargs: pytest.fail("SANY-invalid input must stop before TLAPM"),
    )
    monkeypatch.setattr(sys, "argv", _argv(source, output, mode))

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 1
    assert "SANY-STATUS: invalid" in output.read_text()
    assert "[SANY-INVALID]" in output.read_text()
    assert "Non-unique fields in constructor" in (tmp_path / "sany.log").read_text()


@pytest.mark.parametrize("mode", ["proof-completion", "proof-from-scratch"])
def test_sany_unavailable_is_error_in_every_mode(tmp_path, monkeypatch, mode):
    source = tmp_path / "Foo.tla"
    source.write_text("---- MODULE Foo ----\nTHEOREM Ok == TRUE PROOF OBVIOUS\n====\n")
    output = tmp_path / "check.result"
    unavailable = SanyRun(
        SanyStatus.UNAVAILABLE,
        ("missing-run.sh",),
        None,
        "",
        "run.sh missing",
        "SANY could not run: run.sh missing",
    )
    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: unavailable)
    monkeypatch.setattr(
        check_proof,
        "run_killgroup",
        lambda *_args, **_kwargs: pytest.fail("SANY-unavailable input must stop before TLAPM"),
    )
    monkeypatch.setattr(sys, "argv", _argv(source, output, mode))

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 3
    assert "SANY-STATUS: unavailable" in output.read_text()
    assert "SANY validation unavailable" in output.read_text()


def test_sany_only_unavailable_is_error(tmp_path, monkeypatch):
    source = tmp_path / "Foo.tla"
    source.write_text("---- MODULE Foo ----\n====\n")
    output = tmp_path / "check.result"
    unavailable = SanyRun(SanyStatus.UNAVAILABLE, ("sany",), None, "", "", "tool missing")
    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: unavailable)
    monkeypatch.setattr(sys, "argv", _argv(source, output, "proof-completion", "--sany-only"))

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 3


def test_sany_only_default_output_writes_target_specific_log(tmp_path, monkeypatch):
    source = tmp_path / "Foo.tla"
    source.write_text("---- MODULE Foo ----\n====\n")
    valid = SanyRun(SanyStatus.VALID, ("sany",), 0, "dump", "", "", {})
    monkeypatch.setattr(check_proof, "check_sany_valid", lambda _path: valid)
    monkeypatch.setattr(
        sys,
        "argv",
        ["check_proof", str(source), "--mode", "proof-completion", "--no-container", "--sany-only"],
    )

    with pytest.raises(SystemExit) as exc_info:
        check_proof.main()

    assert exc_info.value.code == 0
    assert (tmp_path / "Foo.sany.log").is_file()
    assert not (tmp_path / "sany.log").exists()


def test_standalone_sany_logs_do_not_overwrite_each_other(tmp_path):
    first = SanyRun(SanyStatus.VALID, ("sany",), 0, "first", "", "", {})
    second = SanyRun(SanyStatus.INVALID, ("sany",), 3, "", "second", "bad")

    first_log = check_proof.write_sany_log(first, str(tmp_path / "A.result"))
    second_log = check_proof.write_sany_log(second, str(tmp_path / "B.result"))

    assert first_log != second_log
    assert (tmp_path / "A.sany.log").read_text().startswith("status: valid")
    assert (tmp_path / "B.sany.log").read_text().startswith("status: invalid")
