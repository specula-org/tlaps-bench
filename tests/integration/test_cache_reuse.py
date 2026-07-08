"""End-to-end fingerprint-cache behavior for the real checker."""

import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CHECK = os.path.join(REPO, "src", "common", "check_proof.py")
SRS = os.path.join(REPO, "src", "dataset", "sany-dump", "run.sh")

GOOD_TLA = "---- MODULE Good ----\nEXTENDS Integers, TLAPS\nTHEOREM Target == 1 + 1 = 2\nPROOF OBVIOUS\n====\n"

VERDICT_RE = re.compile(r"^\s*(PASS|FAIL)\b", re.MULTILINE)


def _tlapm():
    for c in ("/opt/tlapm/bin/tlapm", os.path.expanduser("~/.tlapm/bin/tlapm")):
        if os.path.isfile(c):
            return c
    return None


def _make_workspace():
    w = tempfile.mkdtemp(prefix="cachereuse_")
    with open(os.path.join(w, "Good.tla"), "w") as f:
        f.write(GOOD_TLA)
    subprocess.run(["git", "init", "-q"], cwd=w)
    subprocess.run(["git", "add", "-A"], cwd=w)
    subprocess.run(
        ["git", "-c", "user.email=b@b", "-c", "user.name=b", "commit", "-qm", "baseline"],
        cwd=w,
        capture_output=True,
    )
    return w


def _run_check(w, *extra_args):
    env = {**os.environ, "PYTHONPATH": os.path.join(REPO, "src"), "SANY_RUN_SH": SRS}
    r = subprocess.run(
        [sys.executable, CHECK, "Good.tla", "--mode", "proof-from-scratch", "--timeout", "120", *extra_args],
        cwd=w,
        capture_output=True,
        text=True,
        timeout=300,
        env=env,
    )
    m = VERDICT_RE.search(r.stdout)
    return (m.group(1) if m else "?"), r.stdout


def _fingerprints_path(w):
    return os.path.join(w, ".tlacache", "Good.tlaps", "fingerprints")


def test_default_reuses_cache_beside_target():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = _make_workspace()
    try:
        verdict1, out1 = _run_check(w)
        assert verdict1 == "PASS", f"cold run failed:\n{out1[-800:]}"
        assert os.path.isfile(_fingerprints_path(w)), "no persistent fingerprint cache beside the target"

        verdict2, out2 = _run_check(w)
        assert verdict2 == "PASS", f"warm run diverged from cold run:\n{out2[-800:]}"
    finally:
        shutil.rmtree(w, ignore_errors=True)


def test_no_cache_neither_creates_nor_touches_workspace_cache():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = _make_workspace()
    try:
        verdict, out = _run_check(w, "--no-cache")
        assert verdict == "PASS", f"--no-cache run failed:\n{out[-800:]}"
        assert not os.path.exists(os.path.join(w, ".tlacache")), "--no-cache still wrote a workspace cache"

        os.makedirs(os.path.dirname(_fingerprints_path(w)))
        with open(_fingerprints_path(w), "w") as f:
            f.write("GARBAGE-NOT-A-FINGERPRINT-FILE\n")
        verdict, out = _run_check(w, "--no-cache")
        assert verdict == "PASS", f"--no-cache run failed with workspace cache present:\n{out[-800:]}"
        with open(_fingerprints_path(w)) as f:
            assert f.read() == "GARBAGE-NOT-A-FINGERPRINT-FILE\n", "--no-cache touched the workspace cache"
    finally:
        shutil.rmtree(w, ignore_errors=True)


def test_poisoned_cache_cannot_break_the_check():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    w = _make_workspace()
    try:
        os.makedirs(os.path.dirname(_fingerprints_path(w)))
        with open(_fingerprints_path(w), "w") as f:
            f.write("GARBAGE-NOT-A-FINGERPRINT-FILE\n")
        verdict, out = _run_check(w)
        assert verdict == "PASS", f"corrupt cache broke the default (reusing) run:\n{out[-800:]}"
    finally:
        shutil.rmtree(w, ignore_errors=True)


if __name__ == "__main__":
    import pytest

    sys.exit(pytest.main([__file__, "-q"]))
