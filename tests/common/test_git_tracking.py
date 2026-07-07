"""Unit coverage for the per-check git snapshot on refs/tlaps-check/history."""

import os
import subprocess

from common import check_proof


def _git(w, *argv):
    return subprocess.run(["git", *argv], capture_output=True, text=True, cwd=w)


def _init_repo(tmp_path):
    w = str(tmp_path)
    (tmp_path / "Good.tla").write_text("---- MODULE Good ----\n====\n")
    _git(w, "init", "-q")
    _git(w, "add", "-A")
    _git(w, "-c", "user.email=b@b", "-c", "user.name=b", "commit", "-qm", "baseline")
    return w


def test_snapshot_commits_chain_on_hidden_ref_without_touching_head(tmp_path):
    w = _init_repo(tmp_path)
    fp = os.path.join(w, "Good.tla")
    head_before = _git(w, "rev-parse", "HEAD").stdout
    status_before = _git(w, "status", "--porcelain").stdout

    repo, tree = check_proof.snapshot_worktree(fp)
    assert tree
    c1 = check_proof.record_check_commit(repo, tree, "check_proof Good [proof-completion]: FAIL")
    assert c1
    c2 = check_proof.record_check_commit(repo, tree, "check_proof Good [proof-completion]: PASS")
    assert c2

    log = _git(w, "log", "--format=%H %s", check_proof.GIT_TRACK_REF).stdout.splitlines()
    assert [line.split()[0] for line in log] == [c2, c1]
    assert "PASS" in log[0] and "FAIL" in log[1]
    assert _git(w, "rev-parse", f"{c2}^").stdout.strip() == c1

    # HEAD, index, and worktree are untouched — the tracking is invisible.
    assert _git(w, "rev-parse", "HEAD").stdout == head_before
    assert _git(w, "status", "--porcelain").stdout == status_before
    # The snapshot chain never reaches HEAD, so the root-commit cheat baseline
    # (git rev-list --max-parents=0 HEAD) cannot be affected.
    roots = _git(w, "rev-list", "--max-parents=0", "HEAD").stdout.split()
    assert c1 not in roots and c2 not in roots


def test_snapshot_captures_uncommitted_files_but_not_tlacache(tmp_path):
    w = _init_repo(tmp_path)
    (tmp_path / "New.tla").write_text("uncommitted\n")
    os.makedirs(os.path.join(w, ".tlacache", "Good.tlaps"))
    with open(os.path.join(w, ".tlacache", "Good.tlaps", "fingerprints"), "w") as f:
        f.write("binary-cache-state\n")

    _repo, tree = check_proof.snapshot_worktree(os.path.join(w, "Good.tla"))
    names = _git(w, "ls-tree", "-r", "--name-only", tree).stdout
    assert "Good.tla" in names
    assert "New.tla" in names
    assert ".tlacache" not in names


def test_snapshot_outside_a_repo_is_a_noop(tmp_path):
    fp = tmp_path / "Good.tla"
    fp.write_text("---- MODULE Good ----\n====\n")
    assert check_proof.snapshot_worktree(str(fp)) == (None, None)


def test_record_commit_failure_returns_none(tmp_path):
    w = _init_repo(tmp_path)
    assert check_proof.record_check_commit(w, "0" * 40, "msg") is None


def test_flag_and_env_coupled_between_cli_and_checker():
    # The disable knobs the docs promise must exist verbatim in the source.
    with open(os.path.join(os.path.dirname(__file__), "..", "..", "src", "common", "check_proof.py")) as f:
        src = f.read()
    assert '"--no-git-track"' in src
    assert "TLAPS_NO_GIT_TRACK" in src


if __name__ == "__main__":
    import sys

    import pytest

    sys.exit(pytest.main([__file__, "-q"]))
