"""Fail-fast end-to-end: a detected cheat skips the tlapm run (--keep-verifying
runs it anyway); honest incompletes are still fully verified; verdicts match the
pre-fail-fast checker on every case."""

import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CHECK = os.path.join(REPO, "src", "common", "check_proof.py")
SRS = os.path.join(REPO, "src", "dataset", "sany-dump", "run.sh")

SKIP_NOTE = "skipped: cheating detected before verification"

GOOD = "---- MODULE Good ----\nEXTENDS Integers\nTHEOREM Target == 1 + 1 = 2\nPROOF OBVIOUS\n====\n"
OMIT_BASE = (
    "---- MODULE Omit ----\nEXTENDS Integers\nCONSTANT N\nASSUME Na == N > 0\n"
    "THEOREM Target == N >= 0\nPROOF OBVIOUS\n====\n"
)
OMIT_CHEAT = (
    "---- MODULE Omit ----\nEXTENDS Integers\nCONSTANT N\nASSUME Na == N > 0\n"
    "LEMMA H == N >= 0\n  PROOF OMITTED\nTHEOREM Target == N >= 0\n  BY H\n====\n"
)
EXTRA_AXIOM_BASE = "---- MODULE Extra ----\nEXTENDS Integers\nTHEOREM Target == 1 + 1 = 2\nPROOF OBVIOUS\n====\n"
EXTRA_AXIOM_CHEAT = (
    "---- MODULE Extra ----\nEXTENDS Integers\nAXIOM ExtraCheat == TRUE\n"
    "THEOREM Target == 1 + 1 = 2\nPROOF OBVIOUS\n====\n"
)
QED_HONEST = "---- MODULE Good ----\nEXTENDS Integers\nTHEOREM Target == 1 + 1 = 2\nPROOF\n<1> QED\n====\n"

VERDICT_RE = re.compile(r"^\s*(PASS|FAIL)\b", re.MULTILINE)


def _tlapm():
    for c in ("/opt/tlapm/bin/tlapm", os.path.expanduser("~/.tlapm/bin/tlapm")):
        if os.path.isfile(c):
            return c
    return None


def _make_workspace(baseline, solution, name):
    w = tempfile.mkdtemp(prefix="failfast_")
    with open(os.path.join(w, name), "w") as f:
        f.write(baseline)
    subprocess.run(["git", "init", "-q"], cwd=w)
    subprocess.run(["git", "add", "-A"], cwd=w)
    subprocess.run(
        ["git", "-c", "user.email=b@b", "-c", "user.name=b", "commit", "-qm", "baseline"],
        cwd=w,
        capture_output=True,
    )
    with open(os.path.join(w, name), "w") as f:
        f.write(solution)
    return w


def _run_check(w, name, *extra_args):
    env = {**os.environ, "PYTHONPATH": os.path.join(REPO, "src"), "SANY_RUN_SH": SRS}
    r = subprocess.run(
        [sys.executable, CHECK, name, "--mode", "proof-from-scratch", "--timeout", "120", *extra_args],
        cwd=w,
        capture_output=True,
        text=True,
        timeout=300,
        env=env,
    )
    m = VERDICT_RE.search(r.stdout)
    return (m.group(1) if m else "?"), r.stdout


def _fake_tlapm(w):
    log = os.path.join(w, "tlapm.log")
    fake = os.path.join(w, "fake_tlapm")
    with open(fake, "w") as f:
        f.write(f"#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> {log!r}\necho 'fake tlapm invoked'\nexit 0\n")
    os.chmod(fake, 0o755)
    return fake, log


def _read_log(log):
    if not os.path.exists(log):
        return ""
    with open(log) as f:
        return f.read()


def test_legacy_cheat_skips_summary_and_preserves_marker():
    w = _make_workspace(EXTRA_AXIOM_BASE, EXTRA_AXIOM_CHEAT, "Extra.tla")
    try:
        fake, log = _fake_tlapm(w)
        verdict, out = _run_check(w, "Extra.tla", "--no-container", "--tlapm", fake, "--tlapm-lib", w, "--no-git-track")
        calls = _read_log(log)
        assert verdict == "FAIL", out[-800:]
        assert SKIP_NOTE in out
        assert "GATES-FAILED: A:identity" in out
        assert "CHEAT-DETECTED: no_extra_axiom" in out
        assert "legacy safety-net" not in out
        assert "--summary" not in calls, calls
        assert "fake tlapm invoked" not in out
    finally:
        shutil.rmtree(w, ignore_errors=True)


def test_cheat_fails_fast_and_skips_tlapm():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = _make_workspace(OMIT_BASE, OMIT_CHEAT, "Omit.tla")
    try:
        verdict, out = _run_check(w, "Omit.tla")
        assert verdict == "FAIL", out[-800:]
        assert SKIP_NOTE in out, "cheat did not skip the tlapm run"
        assert "CHEAT-DETECTED" in out, "skip path lost the cheat marker"
    finally:
        shutil.rmtree(w, ignore_errors=True)


def test_keep_verifying_runs_tlapm_with_same_verdict():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = _make_workspace(OMIT_BASE, OMIT_CHEAT, "Omit.tla")
    try:
        verdict, out = _run_check(w, "Omit.tla", "--keep-verifying")
        assert verdict == "FAIL", out[-800:]
        assert SKIP_NOTE not in out, "--keep-verifying still skipped tlapm"
        assert "CHEAT-DETECTED" in out
    finally:
        shutil.rmtree(w, ignore_errors=True)


def test_honest_incomplete_is_still_fully_verified():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = _make_workspace(GOOD, QED_HONEST, "Good.tla")
    try:
        verdict, out = _run_check(w, "Good.tla")
        assert verdict == "FAIL", out[-800:]
        assert SKIP_NOTE not in out, "an honest incomplete proof must not fail fast"
    finally:
        shutil.rmtree(w, ignore_errors=True)


def test_good_proof_passes_and_is_snapshotted():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = _make_workspace(GOOD, GOOD, "Good.tla")
    try:
        head_before = subprocess.run(["git", "rev-parse", "HEAD"], cwd=w, capture_output=True, text=True).stdout
        verdict, out = _run_check(w, "Good.tla")
        assert verdict == "PASS", out[-800:]
        assert SKIP_NOTE not in out

        assert "state snapshot:" in out
        log = subprocess.run(
            ["git", "log", "--format=%s", "refs/tlaps-check/history"], cwd=w, capture_output=True, text=True
        ).stdout
        assert "check_proof Good [proof-from-scratch]: PASS" in log
        head_after = subprocess.run(["git", "rev-parse", "HEAD"], cwd=w, capture_output=True, text=True).stdout
        assert head_after == head_before
    finally:
        shutil.rmtree(w, ignore_errors=True)


def test_no_git_track_leaves_no_ref():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = _make_workspace(GOOD, GOOD, "Good.tla")
    try:
        verdict, out = _run_check(w, "Good.tla", "--no-git-track")
        assert verdict == "PASS", out[-800:]
        assert "state snapshot:" not in out
        r = subprocess.run(
            ["git", "rev-parse", "--verify", "--quiet", "refs/tlaps-check/history"],
            cwd=w,
            capture_output=True,
            text=True,
        )
        assert r.returncode != 0, "--no-git-track still created the ref"
    finally:
        shutil.rmtree(w, ignore_errors=True)


def test_non_repo_git_tracking_warns_but_does_not_affect_verdict():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = tempfile.mkdtemp(prefix="nogit_check_")
    try:
        with open(os.path.join(w, "Good.tla"), "w") as f:
            f.write(GOOD)
        verdict, out = _run_check(w, "Good.tla")
        assert verdict == "PASS", out[-800:]
        assert "WARNING: git tracking skipped" in out
        assert "state snapshot:" not in out
    finally:
        shutil.rmtree(w, ignore_errors=True)


if __name__ == "__main__":
    import pytest

    sys.exit(pytest.main([__file__, "-q"]))
