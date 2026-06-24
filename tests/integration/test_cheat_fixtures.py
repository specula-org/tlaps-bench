"""End-to-end "known-cheat" regression suite (W7 — standing red team).

Each case crafts a baseline benchmark + an agent solution in a throwaway git
workspace and runs the REAL checker (src/common/check_proof.py) end-to-end,
asserting the binary verdict. This locks in every gate: a future change that
re-opens a known cheat vector turns this suite red.

Needs tlapm (~/.tlapm) + Java SANY; silently no-ops when tlapm is absent so it
does not fail an environment without it (CI installs tlapm via install_deps).

Run: PYTHONPATH=src python3 tests/integration/test_cheat_fixtures.py
(or:  PYTHONPATH=src python3 -m pytest tests/integration/test_cheat_fixtures.py)
"""

import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CHECK = os.path.join(REPO, "src", "common", "check_proof.py")
SRS = os.path.join(REPO, "src", "dataset", "sany-dump", "run.sh")


def _tlapm():
    for c in ("/opt/tlapm/bin/tlapm", os.path.expanduser("~/.tlapm/bin/tlapm")):
        if os.path.isfile(c):
            return c
    return None


# Each case: baseline (git-root / original) + solution (working tree) files.
# expect_pass=True  → a genuine proof that must PASS.
# expect_pass=False → a known cheat / incomplete that must FAIL (binary; no CHEAT).
CASES = [
    {
        "name": "correct_l2",
        "level": 2,
        "target": "Good.tla",
        "baseline": {"Good.tla": "---- MODULE Good ----\nEXTENDS Integers\nTHEOREM G == 1 + 1 = 2\nPROOF OBVIOUS\n====\n"},
        "solution": {"Good.tla": "---- MODULE Good ----\nEXTENDS Integers\nTHEOREM G == 1 + 1 = 2\n  OBVIOUS\n====\n"},
        "expect_pass": True,
    },
    {
        "name": "sany_invalid_shadow",
        "level": 2,
        "target": "Shadow.tla",
        "baseline": {
            "M.tla": "---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\n====\n",
            "Shadow.tla": "---- MODULE Shadow ----\nEXTENDS M\nTHEOREM T == TRUE\nPROOF OBVIOUS\n====\n",
        },
        "solution": {
            "M.tla": "---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\n====\n",
            "Shadow.tla": "---- MODULE Shadow ----\nEXTENDS M\nOp(x) == x + 1\nTHEOREM T == Op(0) = 1\n  OBVIOUS\n====\n",
        },
        "expect_pass": False,
    },
    {
        "name": "admitted_goal",
        "level": 2,
        "target": "Admit.tla",
        "baseline": {"Admit.tla": "---- MODULE Admit ----\nEXTENDS Integers\nCONSTANT N\nASSUME Na == N > 0\nTHEOREM Target == N > 0\nPROOF OBVIOUS\n====\n"},
        "solution": {"Admit.tla": "---- MODULE Admit ----\nEXTENDS Integers\nCONSTANT N\nASSUME Na == N > 0\nLEMMA Goal == N > 0\nTHEOREM Target == N > 0\n  BY Goal\n====\n"},
        "expect_pass": False,
    },
    {
        "name": "added_proof_omitted",
        "level": 2,
        "target": "Omit.tla",
        "baseline": {"Omit.tla": "---- MODULE Omit ----\nEXTENDS Integers\nCONSTANT N\nASSUME Na == N > 0\nTHEOREM Target == N >= 0\nPROOF OBVIOUS\n====\n"},
        "solution": {"Omit.tla": "---- MODULE Omit ----\nEXTENDS Integers\nCONSTANT N\nASSUME Na == N > 0\nLEMMA H == N >= 0\n  PROOF OMITTED\nTHEOREM Target == N >= 0\n  BY H\n====\n"},
        "expect_pass": False,
    },
    {
        "name": "bare_qed",
        "level": 2,
        "target": "Qed.tla",
        "baseline": {"Qed.tla": "---- MODULE Qed ----\nEXTENDS Integers\nTHEOREM Target == 1 + 1 = 2\nPROOF OBVIOUS\n====\n"},
        "solution": {"Qed.tla": "---- MODULE Qed ----\nEXTENDS Integers\nTHEOREM Target == 1 + 1 = 2\nPROOF\n<1> QED\n====\n"},
        "expect_pass": False,
    },
]

VERDICT_RE = re.compile(r"^\s*(PASS|FAIL)\b", re.MULTILINE)


def _run_case(case):
    """Build the workspace, run check_proof.py, return (verdict, output)."""
    w = tempfile.mkdtemp(prefix="cheatfix_")
    try:
        for name, content in case["baseline"].items():
            with open(os.path.join(w, name), "w") as f:
                f.write(content)
        subprocess.run(["git", "init", "-q"], cwd=w)
        subprocess.run(["git", "add", "-A"], cwd=w)
        subprocess.run(
            ["git", "-c", "user.email=b@b", "-c", "user.name=b", "commit", "-qm", "baseline"],
            cwd=w, capture_output=True,
        )
        for name, content in case["solution"].items():  # overlay the agent solution
            with open(os.path.join(w, name), "w") as f:
                f.write(content)
        env = {**os.environ, "PYTHONPATH": os.path.join(REPO, "src"), "SANY_RUN_SH": SRS}
        r = subprocess.run(
            [sys.executable, CHECK, case["target"], "--level", str(case["level"]), "--timeout", "120"],
            cwd=w, capture_output=True, text=True, timeout=300, env=env,
        )
        m = VERDICT_RE.search(r.stdout)
        return (m.group(1) if m else "?"), r.stdout
    finally:
        import shutil

        shutil.rmtree(w, ignore_errors=True)


def _check(case):
    if _tlapm() is None:
        print(f"  SKIP (no tlapm)  {case['name']}")
        return True
    verdict, out = _run_case(case)
    want = "PASS" if case["expect_pass"] else "FAIL"
    ok = verdict == want
    print(f"  [{'ok' if ok else 'FAIL':4}] {case['name']:22} want={want} got={verdict}")
    if not ok:
        print("    --- output tail ---")
        for line in out.splitlines()[-12:]:
            print(f"    {line}")
    assert ok, f"{case['name']}: expected {want}, got {verdict}"
    return ok


def test_correct_l2():
    _check(CASES[0])


def test_sany_invalid_shadow():
    _check(CASES[1])


def test_admitted_goal():
    _check(CASES[2])


def test_added_proof_omitted():
    _check(CASES[3])


def test_bare_qed():
    _check(CASES[4])


if __name__ == "__main__":
    if _tlapm() is None:
        print("SKIPPED: tlapm not installed (~/.tlapm or /opt/tlapm)")
        sys.exit(0)
    for c in CASES:
        _check(c)
    print("all cheat-fixture cases passed")
