"""runner continuation rounds (--max-continuations) — repair, don't restart.

A genuine non-PASS may be an early stop rather than an inability: opt-in
continuation re-runs the agent in the SAME workspace (the partial proof is the
input) with a continuation prompt, re-grading each round, stopping at the first
PASS or at the budget. pass@1 must stay untouched: check_verdict keeps the FIRST
attempt's verdict and rounds are recorded separately under "continuations".
Fakes stand in for the agent and grader (see test_infra_retry.py).

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_continuation.py
"""

import json
import os

from evaluator import runner
from evaluator.backends.agentic import AgenticBackend
from evaluator.termination import TerminationReason

BENCH_TEXT = "---- MODULE Bar ----\n====\n"

# One clean copilot terminal event: classifies as a genuine, completed run.
CLEAN_EVENTS = [{"type": "result", "exitCode": 0}]

# The observed startup shape: nonzero exit, no events, error only on stderr.
STARTUP = {"exit": 1, "stderr": "Error: Failed to load models\n"}
# A genuine attempt whose proof simply didn't verify.
GENUINE = {"exit": 0, "events": CLEAN_EVENTS, "out_tokens": 500}


class _ScriptedBackend(AgenticBackend):
    """Backend whose per-call behavior is scripted (see _install_agent)."""

    name = "copilot"

    def __init__(self):
        self.out_tokens = 0  # set by the fake agent for the current call

    def parse_output(self, jsonl_path):
        return ("", 0, self.out_tokens)

    def build_command(self, workspace, result_dir):
        return ["fake-agent"]

    def detect_quota_block(self, jsonl_path):
        return None


class _FakeMode:
    name = "proof-completion"

    def __init__(self, bench_dir):
        self._bench_dir = bench_dir

    def benchmark_dir(self):
        return self._bench_dir

    def get_dependencies(self, benchmark_path):
        return []

    def checker_binary_path(self):
        return "/bin/true"

    def build_prompt(self, basename, tlapm_path, tlapm_lib):
        return "prove it"

    def build_continuation_prompt(self, basename, tlapm_path, tlapm_lib):
        return "continue it"


def _work_item(tmp_path, backend, max_continuations=0, infra_retries=0):
    bench_dir = tmp_path / "bench"
    bench_path = bench_dir / "Foo" / "Bar.tla"
    os.makedirs(bench_path.parent, exist_ok=True)
    bench_path.write_text(BENCH_TEXT)
    return runner.WorkItem(
        benchmark_path=str(bench_path),
        output_dir=str(tmp_path / "out"),
        timeout=10,
        check_timeout=10,
        backend=backend,  # ty:ignore[invalid-argument-type]
        mode=_FakeMode(str(bench_dir)),  # ty:ignore[invalid-argument-type]
        tlapm_path="/bin/true",
        tlapm_lib="",
        infra_retries=infra_retries,
        max_continuations=max_continuations,
    )


def _install_agent(monkeypatch, backend, calls_spec):
    """Patch _run_backend_local with a scripted agent: one spec dict per call
    ({"exit": int, "events": [...], "stderr": str, "out_tokens": int,
    "mutate": fn(workspace)}), recording workspace/prompt/canonical per call."""
    calls = {"n": 0, "workspaces": [], "prompts": [], "agent_dirs": [], "canonical_dirs": []}

    def fake_run(
        item, backend_, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        spec = calls_spec[calls["n"]]
        calls["n"] += 1
        calls["workspaces"].append(workspace)
        calls["prompts"].append(prompt)
        calls["agent_dirs"].append(agent_dir)
        calls["canonical_dirs"].append(canonical_dir)
        with open(agent_jsonl, "w") as f:
            for ev in spec.get("events", []):
                f.write(json.dumps(ev) + "\n")
        if spec.get("stderr"):
            with open(os.path.join(agent_dir, "stderr.txt"), "w") as f:
                f.write(spec["stderr"])
        result["agent_exit"] = spec.get("exit", 0)
        backend.out_tokens = spec.get("out_tokens", 0)
        if "mutate" in spec:
            spec["mutate"](workspace)

    monkeypatch.setattr(runner, "_run_backend_local", fake_run)
    return calls


def _install_grader(monkeypatch, verdicts):
    """Patch _run_grader_local with one scripted verdict per grading call."""
    calls = {"n": 0, "grading_dirs": []}

    def fake_grader(item, workspace, basename, grading_dir, check_result_path, result, canonical_dir=None):
        result["check_verdict"] = verdicts[calls["n"]]
        calls["n"] += 1
        calls["grading_dirs"].append(grading_dir)

    monkeypatch.setattr(runner, "_run_grader_local", fake_grader)
    return calls


def _no_sleep(monkeypatch):
    sleeps = []
    monkeypatch.setattr(runner.time, "sleep", lambda s: sleeps.append(s))
    return sleeps


def test_continues_in_same_workspace_until_pass(tmp_path, monkeypatch):
    # FAIL, FAIL, PASS with budget 3: two continuation rounds, then stop early.
    # The workspace (and the partial proof in it) must persist across rounds,
    # and check_verdict must keep the FIRST attempt's verdict (pass@1).
    seen = []

    def scribble(workspace):
        with open(os.path.join(workspace, "Bar.tla"), "w") as f:
            f.write("PARTIAL PROOF")

    def check(workspace):
        with open(os.path.join(workspace, "Bar.tla")) as f:
            seen.append(f.read())

    backend = _ScriptedBackend()
    agent = _install_agent(
        monkeypatch, backend, [dict(GENUINE, mutate=scribble), dict(GENUINE, mutate=check), dict(GENUINE, mutate=check)]
    )
    grader = _install_grader(monkeypatch, ["FAIL", "FAIL", "PASS"])
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=3))

    assert agent["n"] == 3 and grader["n"] == 3
    assert len(set(agent["workspaces"])) == 1  # same workspace every round
    assert seen == ["PARTIAL PROOF", "PARTIAL PROOF"]
    assert result["check_verdict"] == "FAIL"  # pass@1 untouched
    assert [r["check_verdict"] for r in result["continuations"]] == ["FAIL", "PASS"]
    assert [r["round"] for r in result["continuations"]] == [1, 2]
    # Round artifacts land under continuations/round-N/, next to agent/ + grading/.
    out = tmp_path / "out" / "Foo" / "Bar"
    for rnd in (1, 2):
        round_dir = out / "continuations" / f"round-{rnd}"
        assert (round_dir / "prompt.txt").read_text() == "continue it"
        assert (round_dir / "output.jsonl").is_file()
        assert (round_dir / "solution.tla").read_text() == "PARTIAL PROOF"
    assert grader["grading_dirs"] == [
        str(out / "grading"),
        str(out / "continuations" / "round-1"),
        str(out / "continuations" / "round-2"),
    ]
    saved = json.loads((out / "result.json").read_text())
    assert saved["check_verdict"] == "FAIL"
    assert [r["check_verdict"] for r in saved["continuations"]] == ["FAIL", "PASS"]


def test_stops_at_continuation_budget(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [GENUINE] * 3)
    grader = _install_grader(monkeypatch, ["FAIL"] * 3)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=2))
    assert agent["n"] == 3 and grader["n"] == 3
    assert result["check_verdict"] == "FAIL"
    assert [r["check_verdict"] for r in result["continuations"]] == ["FAIL", "FAIL"]
    assert result["max_continuations"] == 2  # the metric must be able to state its budget


def test_first_attempt_pass_never_continued(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [GENUINE])
    _install_grader(monkeypatch, ["PASS"])
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=3))
    assert agent["n"] == 1
    assert result["check_verdict"] == "PASS"
    assert "continuations" not in result
    assert result["max_continuations"] == 3  # run-level budget stamped even without rounds


def test_disabled_by_default(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [GENUINE])
    _install_grader(monkeypatch, ["FAIL"])
    result = runner.run_single_benchmark(_work_item(tmp_path, backend))
    assert agent["n"] == 1
    assert "continuations" not in result
    assert "max_continuations" not in result


def test_non_genuine_first_attempt_not_continued(tmp_path, monkeypatch):
    # A first attempt cut short by infra was never a genuine non-PASS: there is
    # no partial proof to build on, so continuation must not fire (--resume owns
    # the rerun of non-genuine results).
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [STARTUP])
    grader = _install_grader(monkeypatch, [])
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=3))
    assert agent["n"] == 1 and grader["n"] == 0
    assert result["termination_reason"] == TerminationReason.INFRA_ERROR
    assert "continuations" not in result
    assert result["max_continuations"] == 3  # budget still recorded on early exits


def test_continuation_rounds_use_continuation_prompt(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [GENUINE] * 2)
    _install_grader(monkeypatch, ["FAIL", "PASS"])
    runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=1))
    assert agent["prompts"] == ["prove it", "continue it"]


def test_round_startup_failure_retried_in_place(tmp_path, monkeypatch):
    # A 0-token startup death in a continuation round leaves the workspace (and
    # its partial proof) untouched, so the round retries in place — same
    # workspace, no consumed continuation — and its evidence is stashed.
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [GENUINE, STARTUP, GENUINE])
    grader = _install_grader(monkeypatch, ["FAIL", "PASS"])
    sleeps = _no_sleep(monkeypatch)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=1, infra_retries=1))
    assert agent["n"] == 3 and grader["n"] == 2
    assert len(set(agent["workspaces"])) == 1
    # Same rule as first-attempt retries: each attempt gets a fresh canonical
    # snapshot (a failed attempt's copy must never reach a retry or the grader).
    assert agent["canonical_dirs"][1] != agent["canonical_dirs"][2]
    assert len(sleeps) == 1 and sleeps[0] >= 15
    rnd = result["continuations"][0]
    assert rnd["check_verdict"] == "PASS"
    assert rnd["infra_retries"] == 1
    assert rnd["infra_retry_reasons"] == ["Error: Failed to load models"]
    stashed = tmp_path / "out" / "Foo" / "Bar" / "continuations" / "round-1" / "attempts" / "attempt-0"
    assert "Failed to load models" in (stashed / "stderr.txt").read_text()


def test_round_infra_exhaustion_stops_chain_keeps_first_verdict(tmp_path, monkeypatch):
    # Infra noise must not eat the budget round after round, and must never
    # touch the genuine first-attempt verdict.
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [GENUINE, STARTUP, STARTUP])
    grader = _install_grader(monkeypatch, ["FAIL"])
    _no_sleep(monkeypatch)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=3, infra_retries=1))
    assert agent["n"] == 3 and grader["n"] == 1  # never grade an untouched round
    assert result["check_verdict"] == "FAIL"
    assert result["termination_reason"] == TerminationReason.OK
    assert len(result["continuations"]) == 1  # chain stopped, rounds 2-3 not run
    rnd = result["continuations"][0]
    assert rnd["check_verdict"] == "ERROR"
    assert rnd["termination_reason"] == TerminationReason.INFRA_ERROR
    assert "exhausted infra retries" in rnd["error"]


def test_round_quota_exhaustion_stops_chain(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [GENUINE])
    grader = _install_grader(monkeypatch, ["FAIL"])
    quota_answers = iter([True, False])  # first attempt runs, round 1 is quota-capped
    monkeypatch.setattr(
        runner.quota, "run_with_quota_retry", lambda run, block, **k: next(quota_answers) and (run() or True)
    )
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=3))
    assert agent["n"] == 1 and grader["n"] == 1
    assert result["check_verdict"] == "FAIL"
    assert result["termination_reason"] == TerminationReason.OK
    rnd = result["continuations"][0]
    assert rnd["check_verdict"] == "ERROR"
    assert rnd["agent_exit"] == -3  # same quota sentinel the first attempt records
    assert rnd["termination_reason"] == TerminationReason.QUOTA_EXHAUSTED
    assert len(result["continuations"]) == 1


def test_stale_agent_check_not_copied_into_round(tmp_path, monkeypatch):
    # The in-workspace self-check file survives across rounds (useful context
    # for the agent), but a round's agent_check.result artifact must only
    # record a check THAT round actually ran — never round k-1's stale file.
    def write_check(text, mtime=None):
        def mutate(workspace):
            path = os.path.join(workspace, "Bar.result")
            with open(path, "w") as f:
                f.write(text)
            if mtime is not None:
                os.utime(path, (mtime, mtime))

        return mutate

    backend = _ScriptedBackend()
    _install_agent(
        monkeypatch,
        backend,
        [
            dict(GENUINE, mutate=write_check("round0 check", mtime=1_000_000)),
            GENUINE,  # round 1: agent never re-ran its self-check
            dict(GENUINE, mutate=write_check("round2 check", mtime=2_000_000)),
        ],
    )
    _install_grader(monkeypatch, ["FAIL", "FAIL", "PASS"])
    runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=3))

    out = tmp_path / "out" / "Foo" / "Bar"
    assert (out / "grading" / "agent_check.result").read_text() == "round0 check"
    assert not (out / "continuations" / "round-1" / "agent_check.result").exists()
    assert (out / "continuations" / "round-2" / "agent_check.result").read_text() == "round2 check"


def test_costs_accumulate_into_top_level(tmp_path, monkeypatch):
    # Verdict fields stay first-attempt; cost fields cover the whole chain.
    backend = _ScriptedBackend()
    _install_agent(monkeypatch, backend, [dict(GENUINE, out_tokens=500), dict(GENUINE, out_tokens=300)])
    _install_grader(monkeypatch, ["FAIL", "PASS"])
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, max_continuations=1))
    assert result["output_tokens"] == 800
    assert result["continuations"][0]["output_tokens"] == 300


def test_resume_skips_benchmarks_recovered_by_continuation():
    def _r(name, verdict, cont_verdicts=None, termination="OK"):
        out = {"benchmark": name, "check_verdict": verdict, "termination_reason": termination}
        if cont_verdicts is not None:
            out["continuations"] = [{"round": i + 1, "check_verdict": v} for i, v in enumerate(cont_verdicts)]
        return out

    results = [
        _r("recovered.tla", "FAIL", cont_verdicts=["FAIL", "PASS"]),
        _r("still-failing.tla", "FAIL", cont_verdicts=["FAIL", "FAIL"]),
        _r("plain-pass.tla", "PASS"),
        _r("plain-fail.tla", "FAIL"),
    ]
    assert runner._resume_done_benchmarks(results) == {"recovered.tla", "plain-pass.tla"}


def _summary_result(name, cont_rounds=None, **kw):
    out = {
        "benchmark": name,
        "check_verdict": "FAIL",
        "time_secs": 0,
        "input_tokens": 0,
        "output_tokens": 0,
        "termination_reason": "OK",
    }
    if cont_rounds is not None:
        out["max_continuations"] = 3
        out["continuations"] = cont_rounds
    out.update(kw)
    return out


def test_summary_reports_continuation_metric_separately(tmp_path):
    results = [
        _summary_result(
            "recovered.tla", cont_rounds=[{"round": 1, "check_verdict": "PASS", "termination_reason": "OK"}]
        ),
        _summary_result("plain-fail.tla"),
    ]
    runner.update_summary(
        results, str(tmp_path), total_benchmarks=2, backend_name="copilot", mode_name="proof-completion"
    )
    summary = (tmp_path / "summary.md").read_text()
    assert "**Pass rate**: 0/2 (0.0%)" in summary  # pass@1 stays first-attempt only
    assert "**Pass rate with continuations (≤3)**: 1/2 (50.0%) — 1 recovered by continuation" in summary
    assert "PASS on continuation 1" in summary


def test_summary_excludes_interrupted_chains_from_continuation_rate(tmp_path):
    # A chain cut by infra/quota is indeterminate: dropped from the continuation
    # rate (numerator AND denominator) and disclosed — never a silent failure.
    results = [
        _summary_result(
            "recovered.tla", cont_rounds=[{"round": 1, "check_verdict": "PASS", "termination_reason": "OK"}]
        ),
        _summary_result(
            "cut-chain.tla",
            cont_rounds=[{"round": 1, "check_verdict": "ERROR", "termination_reason": "QUOTA_EXHAUSTED"}],
        ),
        _summary_result("plain-fail.tla"),
    ]
    runner.update_summary(
        results, str(tmp_path), total_benchmarks=3, backend_name="copilot", mode_name="proof-completion"
    )
    summary = (tmp_path / "summary.md").read_text()
    assert "**Pass rate**: 0/3 (0.0%)" in summary  # cut-chain's genuine first FAIL stays scored
    assert (
        "**Pass rate with continuations (≤3)**: 1/2 (50.0%) — 1 recovered by continuation "
        "(pass@1 above is first-attempt only) · 1 chain(s) infra/quota-cut (excluded — re-run)"
    ) in summary
    assert "continuation chain cut at round 1 (excluded — re-run)" in summary  # per-row note discloses too
