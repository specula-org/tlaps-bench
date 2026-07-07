"""Sharded-verification equivalence: for every outcome class (pass, failed
obligation, honest missing step, GIVEN omitted lemma) a forced --shards run
must produce the same verdict and the same module-wide counts as the
single-run path, with boundaries landing on theorem edges."""

import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CHECK = os.path.join(REPO, "src", "common", "check_proof.py")
SRS = os.path.join(REPO, "src", "dataset", "sany-dump", "run.sh")

FOUR_GOOD = """---- MODULE Four ----
EXTENDS Integers

THEOREM A == 1 + 1 = 2
  OBVIOUS

LEMMA B == 2 + 2 = 4
  OBVIOUS

THEOREM C == 3 + 3 = 6
  OBVIOUS

THEOREM Target == 4 + 4 = 8
  OBVIOUS
====
"""

ONE_BAD = """---- MODULE Bad3 ----
EXTENDS Integers

THEOREM A == 1 + 1 = 2
  OBVIOUS

THEOREM B == 1 + 1 = 3
  OBVIOUS

THEOREM Target == 2 + 2 = 4
  OBVIOUS
====
"""

QED_MID = """---- MODULE Mid ----
EXTENDS Integers

THEOREM A == 1 + 1 = 2
  OBVIOUS

THEOREM Target == 2 + 2 = 4
PROOF
<1> QED
====
"""

OMIT_BASE = """---- MODULE Comp ----
EXTENDS Integers

LEMMA Given == 0 * 0 = 0
PROOF OMITTED

THEOREM Target == 0 * 0 = 0
PROOF OBVIOUS
====
"""
OMIT_SOLUTION = OMIT_BASE.replace("PROOF OBVIOUS", "PROOF BY Given")

VERDICT_RE = re.compile(r"^\s*(PASS|FAIL)\b", re.MULTILINE)
PROVED_RE = re.compile(r"All (\d+) obligations? proved\.")
MISSING_RE = re.compile(r"Proof incomplete in module .*?:\s*(\d+) missing, (\d+) omitted")


def _tlapm():
    for c in ("/opt/tlapm/bin/tlapm", os.path.expanduser("~/.tlapm/bin/tlapm")):
        if os.path.isfile(c):
            return c
    return None


def _run(baseline, solution, name, mode, *extra_args):
    w = tempfile.mkdtemp(prefix="shardeq_")
    try:
        with open(os.path.join(w, name), "w") as f:
            f.write(baseline)
        subprocess.run(["git", "init", "-q"], cwd=w)
        subprocess.run(["git", "add", "-A"], cwd=w)
        subprocess.run(
            ["git", "-c", "user.email=b@b", "-c", "user.name=b", "commit", "-qm", "baseline"],
            cwd=w, capture_output=True,
        )
        with open(os.path.join(w, name), "w") as f:
            f.write(solution)
        env = {**os.environ, "PYTHONPATH": os.path.join(REPO, "src"), "SANY_RUN_SH": SRS}
        r = subprocess.run(
            [sys.executable, CHECK, name, "--mode", mode, "--timeout", "120", *extra_args],
            cwd=w, capture_output=True, text=True, timeout=300, env=env,
        )
        m = VERDICT_RE.search(r.stdout)
        return (m.group(1) if m else "?"), r.stdout
    finally:
        shutil.rmtree(w, ignore_errors=True)


def _assert_equivalent(baseline, solution, name, mode, shards, want):
    single_verdict, single_out = _run(baseline, solution, name, mode)
    sharded_verdict, sharded_out = _run(baseline, solution, name, mode, "--shards", str(shards))
    assert "--- shard" not in single_out
    assert "--- shard 1/" in sharded_out, "forced --shards did not engage sharding"
    assert single_verdict == want, single_out[-800:]
    assert sharded_verdict == want, sharded_out[-800:]
    # Module-wide counts must compose identically over the shard partition.
    assert PROVED_RE.findall(single_out)[-1:] == PROVED_RE.findall(sharded_out)[-1:]
    m_single, m_sharded = MISSING_RE.search(single_out), MISSING_RE.search(sharded_out)
    assert (m_single.groups() if m_single else None) == (m_sharded.groups() if m_sharded else None)
    return single_out, sharded_out


def test_all_pass_case():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    _, sharded_out = _assert_equivalent(FOUR_GOOD, FOUR_GOOD, "Four.tla", "proof-from-scratch", 3, "PASS")
    assert "All 4 obligations proved." in sharded_out


def test_failed_obligation_case():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    _, sharded_out = _assert_equivalent(ONE_BAD, ONE_BAD, "Bad3.tla", "proof-from-scratch", 3, "FAIL")
    assert "1/3 obligations failed." in sharded_out


def test_honest_missing_step_case():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    single_out, sharded_out = _assert_equivalent(QED_MID, QED_MID, "Mid.tla", "proof-from-scratch", 2, "FAIL")
    for out in (single_out, sharded_out):
        assert MISSING_RE.search(out).group(1) == "1", out[-800:]


def test_given_omitted_lemma_case():
    # The omitted GIVEN lemma and the target land in different shards; the
    # range-filtered omitted count must compose and must not fail the proof.
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    single_out, sharded_out = _assert_equivalent(OMIT_BASE, OMIT_SOLUTION, "Comp.tla", "proof-completion", 3, "PASS")
    for out in (single_out, sharded_out):
        assert MISSING_RE.search(out).groups() == ("0", "1"), out[-800:]


def test_shards_request_above_unit_count_clamps():
    if _tlapm() is None:
        print("  SKIP (no tlapm)")
        return
    verdict, out = _run(FOUR_GOOD, FOUR_GOOD, "Four.tla", "proof-from-scratch", "--shards", "99")
    assert verdict == "PASS", out[-800:]
    # 4 unit heads = 4 cut points = at most 5 ranges (preamble + one per unit).
    assert "--- shard 1/5:" in out, "99 shards on a 4-unit file must clamp"


if __name__ == "__main__":
    import pytest

    sys.exit(pytest.main([__file__, "-q"]))
