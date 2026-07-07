"""Unit coverage for sharded verification: shard planning and result composition."""

import os

from common.check_proof import (
    auto_shard_count,
    compose_shard_results,
    parse_strict_status,
    plan_shards,
    regex_unit_heads,
)

# --- planning ---------------------------------------------------------------


def _assert_partition(ranges, total_lines, heads):
    assert ranges[0][0] == 1 and ranges[-1][1] == total_lines
    for (_s1, e1), (s2, _e2) in zip(ranges, ranges[1:], strict=False):
        assert s2 == e1 + 1, "ranges must be contiguous with no gap or overlap"
    assert all(s in heads for s, _ in ranges[1:]), "every boundary must sit on a unit head"


def test_plan_shards_partitions_and_balances():
    heads = list(range(10, 3000, 37))  # synthetic 30k-line-style module, ~80 units
    for n in (1, 2, 3, 7, 16):
        ranges = plan_shards(3000, heads, n)
        _assert_partition(ranges, 3000, heads)
        assert len(ranges) == n
        spans = [e - s + 1 for s, e in ranges]
        assert max(spans) <= 2 * (3000 // n), "shards should be roughly line-balanced"


def test_plan_shards_clamps_to_available_cuts():
    assert plan_shards(100, [], 4) == [(1, 100)]
    assert plan_shards(100, [1], 4) == [(1, 100)]  # a head at line 1 is not a cut
    assert plan_shards(100, [50], 4) == [(1, 49), (50, 100)]
    ranges = plan_shards(10, list(range(2, 11)), 99)
    _assert_partition(ranges, 10, list(range(2, 11)))
    assert len(ranges) == 10


def test_regex_unit_heads_ignores_comments():
    text = "\n".join(
        [
            "---- MODULE M ----",  # 1
            "(* block comment mentioning",  # 2
            "THEOREM NotReal == TRUE",  # 3 — inside block comment
            "*)",  # 4
            "THEOREM Real == TRUE",  # 5
            "\\* LEMMA AlsoNotReal",  # 6 — line comment
            "  LEMMA Indented == TRUE",  # 7
            "====",  # 8
        ]
    )
    assert regex_unit_heads(text) == [5, 7]


def test_auto_shard_count_caps():
    assert auto_shard_count(1) == 1
    assert auto_shard_count(0) == 1
    assert auto_shard_count(10_000) <= max(1, (os.cpu_count() or 2) // 2)
    os.environ["TLAPS_SHARD_MEM_MB"] = str(2**30)  # absurd per-shard budget
    try:
        assert auto_shard_count(10_000) == 1
    finally:
        del os.environ["TLAPS_SHARD_MEM_MB"]


# --- composition ------------------------------------------------------------
# Shard outputs below mimic real `tlapm --strict --toolbox` output (tlapm 80172c6).

CLEAN = "[INFO]: All 2 obligations proved.\n@!!BEGIN\n@!!type:obligationsnumber\n@!!count:2\n@!!END"
CLEAN1 = "[INFO]: All 1 obligation proved."
EMPTY = "[ERROR]: No proof obligation found for the selected target.\n[INFO]: All 0 obligation proved."
FAILED = "[ERROR]: Could not prove or check:\nZenon error: exhausted\n[ERROR]: 1/2 obligations failed."
MISSING = 'Missing proof at line 9\n[ERROR]: Proof incomplete in module "M": 1 missing, 0 omitted proof step(s).'
OMITTED = '[ERROR]: Proof incomplete in module "M": 0 missing, 2 omitted proof step(s).\n' + CLEAN1


def test_compose_all_clean():
    out, exit_code = compose_shard_results([(1, 10, 0, CLEAN), (11, 20, 0, CLEAN1)], "M", 600)
    assert exit_code == 0
    assert out.rstrip().endswith("[INFO]: All 3 obligations proved.")
    complete, n_missing, failed = parse_strict_status(exit_code, out)
    assert complete and n_missing == 0 and not failed


def test_compose_empty_shard_is_neutral():
    out, exit_code = compose_shard_results([(1, 10, 12, EMPTY), (11, 20, 0, CLEAN)], "M", 600)
    assert exit_code == 0
    assert "All 2 obligations proved." in out
    assert parse_strict_status(exit_code, out)[0]


def test_compose_all_empty_is_exit_12():
    out, exit_code = compose_shard_results([(1, 10, 12, EMPTY), (11, 20, 12, EMPTY)], "M", 600)
    assert exit_code == 12
    assert not parse_strict_status(exit_code, out)[0]


def test_compose_failed_and_missing_sum_across_shards():
    out, exit_code = compose_shard_results(
        [(1, 10, 10, FAILED), (11, 20, 11, MISSING), (21, 30, 11, MISSING)], "M", 600
    )
    assert exit_code == 10
    assert '[ERROR]: Proof incomplete in module "M": 2 missing, 0 omitted proof step(s).' in out
    assert "[ERROR]: 1/2 obligations failed." in out
    assert "Zenon error" in out, "error detail lines must survive composition"
    complete, n_missing, failed = parse_strict_status(exit_code, out)
    assert not complete and n_missing == 2 and failed


def test_compose_omitted_only_still_completes():
    # GIVEN omitted lemmas: exit 11 with 0 missing is a valid complete proof.
    out, exit_code = compose_shard_results([(1, 10, 11, OMITTED), (11, 20, 0, CLEAN1)], "M", 600)
    assert exit_code == 11
    assert "0 missing, 2 omitted" in out
    assert parse_strict_status(exit_code, out) == (True, 0, False)


def test_compose_exactly_one_canonical_summary():
    # parse_strict_status reads the FIRST "Proof incomplete" and the zero-obligation
    # detector reads the LAST "N obligation" — both must see only module totals.
    out, _ = compose_shard_results([(1, 10, 11, MISSING), (11, 20, 0, CLEAN)], "M", 600)
    assert out.count("Proof incomplete") == 1
    assert out.count("obligations proved") + out.count("obligation proved") == 1


def test_compose_timeout_and_unexpected_rc_never_pass():
    out, exit_code = compose_shard_results([(1, 10, 0, CLEAN), (11, 20, None, "")], "M", 600)
    assert exit_code == -1
    assert "TIMEOUT after 600s" in out
    assert not parse_strict_status(exit_code, out)[0]

    out, exit_code = compose_shard_results([(1, 10, 3, "tlapm ending abnormally"), (11, 20, 0, CLEAN)], "M", 600)
    assert exit_code == 3
    assert not parse_strict_status(exit_code, out)[0]


def test_compose_strips_toolbox_records():
    out, _ = compose_shard_results([(1, 10, 0, CLEAN)], "M", 600)
    assert "@!!" not in out


if __name__ == "__main__":
    import sys

    import pytest

    sys.exit(pytest.main([__file__, "-q"]))
