"""The agent self-check and the grader must read ONE baseline and ONE timeout.

This is the linchpin of the "no fork" guarantee. The grader passes the canonical
snapshot via ``--benchmark-dir`` (an explicit arg) and the tlapm budget via
``--timeout``; the agent's bare ``check_proof_bin <file>`` self-check has no flags,
so it must discover the SAME values from ``$TLAPS_BENCHMARK_DIR`` / ``$TLAPS_CHECK_TIMEOUT``
(set by the runner). If anyone renames the env var on one side, the grader (flag)
keeps working while the agent (env) silently falls back to git-root reconstruction
/ the 600s default — re-opening the very fork these tests pin shut.

Run: PYTHONPATH=src python3 -m pytest tests/common/test_oracle_env_coupling.py
"""

from pathlib import Path

import pytest

from common import check_proof

# The exact env var names the runner WRITES and check_proof READS. The whole
# point of the coupling is that these strings stay identical on both sides.
BENCHMARK_DIR_ENV = "TLAPS_BENCHMARK_DIR"
CHECK_TIMEOUT_ENV = "TLAPS_CHECK_TIMEOUT"


@pytest.fixture(autouse=True)
def _clear_env(monkeypatch):
    # Every test sets its own env explicitly; start from a known-clean slate so a
    # value leaking in from the developer's shell can't mask a regression.
    monkeypatch.delenv(BENCHMARK_DIR_ENV, raising=False)
    monkeypatch.delenv(CHECK_TIMEOUT_ENV, raising=False)


def _canon(tmp_path, name="Foo"):
    """A canonical benchmark dir holding ``<name>.tla`` (what makes a dir qualify)."""
    d = tmp_path / "canon"
    d.mkdir()
    (d / (name + ".tla")).write_text(f"---- MODULE {name} ----\n====\n")
    return str(d)


# --- resolve_benchmark_dir: env path must equal flag path ---------------------


def test_env_path_equals_flag_path(tmp_path, monkeypatch):
    """The agent (env) and the grader (flag) resolve to the IDENTICAL dir.

    This is the equivalence the whole design rests on: feed the same canonical
    snapshot through the grader's ``--benchmark-dir`` arg and through the agent's
    ``$TLAPS_BENCHMARK_DIR`` env, and both must pick it.
    """
    canon = _canon(tmp_path)
    workspace_file = str(tmp_path / "Foo.tla")  # need not exist; only its name matters

    flag_path = check_proof.resolve_benchmark_dir(canon, workspace_file, "Foo")

    monkeypatch.setenv(BENCHMARK_DIR_ENV, canon)
    env_path = check_proof.resolve_benchmark_dir(None, workspace_file, "Foo")

    assert flag_path == canon
    assert env_path == canon
    assert flag_path == env_path, "agent (env) and grader (flag) diverged on the baseline dir"


def test_explicit_flag_wins_over_env(tmp_path, monkeypatch):
    # The grader's explicit --benchmark-dir takes precedence over any env.
    flag_dir = _canon(tmp_path)
    other = tmp_path / "other"
    other.mkdir()
    (other / "Foo.tla").write_text("---- MODULE Foo ----\n====\n")
    monkeypatch.setenv(BENCHMARK_DIR_ENV, str(other))

    assert check_proof.resolve_benchmark_dir(flag_dir, str(tmp_path / "Foo.tla"), "Foo") == flag_dir


def test_dir_without_target_is_rejected(tmp_path, monkeypatch):
    # A dir that does NOT hold <target>.tla must not qualify — otherwise a wrong
    # env would silently "succeed" against the wrong (or empty) baseline. Rejected
    # via both the flag and the env path.
    empty = tmp_path / "empty"
    empty.mkdir()
    wf = str(tmp_path / "Foo.tla")
    assert check_proof.resolve_benchmark_dir(str(empty), wf, "Foo") is None
    monkeypatch.setenv(BENCHMARK_DIR_ENV, str(empty))
    assert check_proof.resolve_benchmark_dir(None, wf, "Foo") is None


def test_none_when_nothing_set(tmp_path):
    # No flag, no env, and no /benchmark/<target>.tla → None (git-root fallback for
    # a developer hand-running the checker outside the harness).
    assert check_proof.resolve_benchmark_dir(None, str(tmp_path / "Zzq_NoSuch.tla"), "Zzq_NoSuch") is None


# --- resolve_timeout: env path must equal flag path ---------------------------


def test_timeout_explicit_wins_over_env(monkeypatch):
    monkeypatch.setenv(CHECK_TIMEOUT_ENV, "999")
    assert check_proof.resolve_timeout(123) == 123  # grader's --timeout wins


def test_timeout_from_env_when_no_flag(monkeypatch):
    # The agent's bare self-check (no --timeout) picks up the grader's budget.
    monkeypatch.setenv(CHECK_TIMEOUT_ENV, "222")
    assert check_proof.resolve_timeout(None) == 222


def test_timeout_default_when_unset():
    assert check_proof.resolve_timeout(None) == 600


def test_timeout_malformed_env_falls_back(monkeypatch):
    monkeypatch.setenv(CHECK_TIMEOUT_ENV, "not-a-number")
    assert check_proof.resolve_timeout(None) == 600


def test_timeout_zero_means_unbounded(monkeypatch):
    assert check_proof.resolve_timeout(0) == 0
    monkeypatch.setenv(CHECK_TIMEOUT_ENV, "0")
    assert check_proof.resolve_timeout(None) == 0
    assert check_proof.effective_timeout(0) is None


def test_effective_timeout_positive_passthrough():
    assert check_proof.effective_timeout(600) == 600


# --- get_baseline_text: canonical first, git fallback -------------------------


def test_baseline_text_from_canonical(tmp_path):
    # When the canonical snapshot holds the file, its text is the baseline —
    # NEVER the agent-writable workspace copy.
    canon = tmp_path / "canon"
    canon.mkdir()
    (canon / "Foo.tla").write_text("CANONICAL\n")
    workspace_foo = tmp_path / "ws" / "Foo.tla"
    workspace_foo.parent.mkdir()
    workspace_foo.write_text("TAMPERED\n")
    assert check_proof.get_baseline_text(str(workspace_foo), str(canon)) == "CANONICAL\n"


def test_baseline_text_git_fallback_without_canonical(tmp_path, monkeypatch):
    # No benchmark_dir → fall back to the git main/master version.
    monkeypatch.setattr(check_proof, "get_main_version", lambda fp: "FROM_GIT")
    assert check_proof.get_baseline_text(str(tmp_path / "Foo.tla"), None) == "FROM_GIT"


def test_baseline_text_git_fallback_when_file_absent(tmp_path, monkeypatch):
    # benchmark_dir is given but lacks the file → fall back to git (don't return
    # None and silently disable the comparison).
    canon = tmp_path / "canon"
    canon.mkdir()
    monkeypatch.setattr(check_proof, "get_main_version", lambda fp: "FROM_GIT")
    assert check_proof.get_baseline_text(str(tmp_path / "Foo.tla"), str(canon)) == "FROM_GIT"


# --- writer<->reader contract: env names must match on BOTH sides ------------


def _src(rel):
    return (Path(__file__).resolve().parents[2] / "src" / rel).read_text(encoding="utf-8")


@pytest.mark.parametrize("env_name", [BENCHMARK_DIR_ENV, CHECK_TIMEOUT_ENV])
def test_env_var_names_coupled_between_runner_and_checker(env_name):
    """Pin the contract: the runner WRITES exactly the env names check_proof READS.

    Renaming the var on one side only is the silent-fork failure mode — it would
    leave the name present in just one file and trip this test.
    """
    runner = _src("evaluator/runner.py")
    checker = _src("common/check_proof.py")
    assert env_name in runner, f"runner.py no longer sets {env_name}"
    assert env_name in checker, f"check_proof.py no longer reads {env_name}"


if __name__ == "__main__":
    import sys

    sys.exit(pytest.main([__file__, "-q"]))
