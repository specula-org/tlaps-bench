"""runner infra-retry loop — retry transient startup failures, never real attempts.

A startup failure (INFRA_ERROR + 0 output tokens: the CLI died before the model
did any work) must be retried on a fresh workspace, and only the final genuine
attempt graded; exhaustion is ERROR/INFRA_ERROR, never a proof FAIL. Fakes stand
in for the agent and grader, so no container, real backend or tlapm is needed.

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_infra_retry.py
"""

import json
import os

import pytest

from evaluator import runner
from evaluator.termination import TerminationReason

BENCH_TEXT = "---- MODULE Bar ----\n====\n"

# One clean copilot terminal event: classifies as a genuine, completed run.
CLEAN_EVENTS = [{"type": "result", "exitCode": 0}]

# The observed startup shape: nonzero exit, no events, error only on stderr.
STARTUP = {"exit": 1, "stderr": "Error: Failed to load models\n\nError: Failed to list models\n"}
# A genuine attempt whose proof simply didn't verify.
GENUINE_FAIL = {"exit": 0, "events": CLEAN_EVENTS, "out_tokens": 500}


class _ScriptedBackend:
    """Backend whose per-attempt behavior is scripted (see _install_agent)."""

    name = "copilot"

    def __init__(self):
        self.out_tokens = 0  # set by the fake agent for the current attempt

    def parse_output(self, jsonl_path):
        return ("", 0, self.out_tokens)

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


def _work_item(tmp_path, backend, infra_retries=3):
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
    )


def _install_agent(monkeypatch, backend, attempts):
    """Patch _run_agent_local with a scripted agent: one spec dict per attempt
    ({"exit": int, "events": [...], "stderr": str, "out_tokens": int,
    "error": str, "mutate": fn(workspace)})."""
    calls = {"n": 0, "workspaces": [], "canonical_dirs": []}

    def fake_run(
        item, backend_, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        spec = attempts[calls["n"]]
        calls["n"] += 1
        calls["workspaces"].append(workspace)
        calls["canonical_dirs"].append(canonical_dir)
        with open(agent_jsonl, "w") as f:
            for ev in spec.get("events", []):
                f.write(json.dumps(ev) + "\n")
        if spec.get("stderr"):
            with open(os.path.join(agent_dir, "stderr.txt"), "w") as f:
                f.write(spec["stderr"])
        result["agent_exit"] = spec.get("exit", 0)
        if spec.get("error"):
            result["error"] = spec["error"]
        backend.out_tokens = spec.get("out_tokens", 0)
        if "mutate" in spec:
            spec["mutate"](workspace)
        if "mutate_canonical" in spec:
            spec["mutate_canonical"](canonical_dir)

    monkeypatch.setattr(runner, "_run_agent_local", fake_run)
    return calls


def _install_grader(monkeypatch, verdict="FAIL", inspect_canonical=None):
    calls = {"n": 0, "canonical_dirs": []}

    def fake_grader(item, workspace, basename, grading_dir, check_result_path, result, canonical_dir=None):
        calls["n"] += 1
        calls["canonical_dirs"].append(canonical_dir)
        if inspect_canonical:
            inspect_canonical(canonical_dir)
        result["check_verdict"] = verdict

    monkeypatch.setattr(runner, "_run_grader_local", fake_grader)
    return calls


def _no_sleep(monkeypatch):
    sleeps = []
    monkeypatch.setattr(runner.time, "sleep", lambda s: sleeps.append(s))
    return sleeps


def _result(benchmark, verdict, termination_reason="OK", **kw):
    out = {
        "benchmark": benchmark,
        "check_verdict": verdict,
        "time_secs": 0,
        "input_tokens": 0,
        "output_tokens": 0,
        "termination_reason": termination_reason,
    }
    out.update(kw)
    return out


def test_summary_excludes_non_genuine_results_from_pass_rate(tmp_path):
    results = [
        _result("genuine-pass.tla", "PASS"),
        _result("genuine-fail.tla", "FAIL"),
        _result("infra-pass.tla", "PASS", termination_reason=TerminationReason.INFRA_ERROR),
        _result("quota-error.tla", "ERROR", termination_reason=TerminationReason.QUOTA_EXHAUSTED),
        _result("skipped.tla", "SKIP"),
    ]
    runner.update_summary(
        results, str(tmp_path), total_benchmarks=5, backend_name="copilot", mode_name="proof-completion"
    )
    summary = (tmp_path / "summary.md").read_text()
    assert "**Pass rate**: 1/2 (50.0%) · 1 skipped · 2 infra/quota-cut (excluded — re-run)" in summary
    assert "`infra-pass.tla` | ✅ PASS" in summary
    assert "INFRA_ERROR (excluded — re-run)" in summary


def test_resume_does_not_skip_non_genuine_pass_results():
    results = [
        _result("genuine-pass.tla", "PASS"),
        _result("legacy-pass.tla", "PASS", termination_reason=None),
        _result("infra-pass.tla", "PASS", termination_reason=TerminationReason.INFRA_ERROR),
        _result("quota-pass.tla", "PASS", termination_reason=TerminationReason.QUOTA_EXHAUSTED),
        _result("skipped.tla", "SKIP"),
        _result("failed.tla", "FAIL"),
    ]
    assert runner._resume_done_benchmarks(results) == {"genuine-pass.tla", "legacy-pass.tla", "skipped.tla"}


def test_resumed_result_replaces_non_genuine_attempt(tmp_path):
    results = [
        _result("already-passed.tla", "PASS"),
        _result("retry.tla", "ERROR", termination_reason=TerminationReason.INFRA_ERROR),
    ]

    runner._record_result(results, _result("retry.tla", "PASS"))
    total_benchmarks = runner._total_benchmark_count(results, {"retry.tla"})
    runner.update_summary(
        results,
        str(tmp_path),
        total_benchmarks=total_benchmarks,
        backend_name="copilot",
        mode_name="proof-completion",
    )

    assert [(r["benchmark"], r["check_verdict"]) for r in results] == [
        ("already-passed.tla", "PASS"),
        ("retry.tla", "PASS"),
    ]
    summary = (tmp_path / "summary.md").read_text()
    assert "**Progress**: 2/2" in summary
    assert "**Pass rate**: 2/2 (100.0%)" in summary
    assert json.loads((tmp_path / "results.json").read_text()) == results


def test_total_benchmark_count_includes_new_filtered_benchmark():
    results = [_result("already-recorded.tla", "PASS")]

    assert runner._total_benchmark_count(results, {"newly-selected.tla"}) == 2


def test_filtered_resume_keeps_cumulative_progress_total(tmp_path, monkeypatch):
    bench_dir = tmp_path / "bench"
    retry = bench_dir / "Suite" / "retry.tla"
    retry.parent.mkdir(parents=True)
    retry.write_text(BENCH_TEXT)

    output_dir = tmp_path / "out"
    output_dir.mkdir()
    previous_results = [
        _result("Suite/already-passed.tla", "PASS"),
        _result("Suite/retry.tla", "PASS"),
    ]
    (output_dir / "results.json").write_text(json.dumps(previous_results))

    backend = _ScriptedBackend()
    mode = _FakeMode(str(bench_dir))
    mode.description = "test mode"
    mode.get_benchmark_files = lambda filter_pattern: [str(retry)]
    monkeypatch.setattr(backend, "check_auth", lambda: None, raising=False)
    monkeypatch.setattr(backend, "default_quota", lambda: (0, 0), raising=False)
    monkeypatch.setattr(backend, "usage_script", lambda: None, raising=False)
    monkeypatch.setattr(runner, "get_backend", lambda *args, **kwargs: backend)
    monkeypatch.setattr(runner, "ensure_tlapm", lambda: None)
    monkeypatch.setattr(runner, "find_tlapm_lib", lambda tlapm_bin: "/tmp/tlapm-lib")
    monkeypatch.setattr(runner, "resolve_paths", lambda: (str(tmp_path), "/bin/true"))
    monkeypatch.setattr(runner, "get_mode", lambda *args: mode)
    monkeypatch.setattr(
        runner.sys,
        "argv",
        [
            "tlaps-bench-run",
            "--no-container",
            "--resume",
            "--filter",
            "retry.tla",
            "--output-dir",
            str(output_dir),
        ],
    )

    runner.main()

    summary = (output_dir / "summary.md").read_text()
    assert "**Progress**: 2/2" in summary
    assert "**Progress**: 2/1" not in summary
    assert json.loads((output_dir / "results.json").read_text()) == previous_results


def test_make_workspace_cleans_up_on_setup_failure(tmp_path, monkeypatch):
    # The temp dir must not leak when workspace setup dies half-way (disk full,
    # unreadable dep) — same guarantee _make_canonical_dir gives.
    created = []
    real_mkdtemp = runner.tempfile.mkdtemp

    def tracking_mkdtemp(**kw):
        d = real_mkdtemp(**kw)
        created.append(d)
        return d

    def broken_copy2(*a, **kw):
        raise OSError("disk full")

    monkeypatch.setattr(runner.tempfile, "mkdtemp", tracking_mkdtemp)
    monkeypatch.setattr(runner.shutil, "copy2", broken_copy2)
    with pytest.raises(OSError):
        runner._make_workspace("copilot", "Bar", str(tmp_path / "Bar.tla"), "Bar.tla", [])
    assert created and not os.path.isdir(created[0])


def test_startup_failure_retried_and_final_attempt_graded(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [STARTUP, GENUINE_FAIL])
    grader = _install_grader(monkeypatch, verdict="FAIL")
    sleeps = _no_sleep(monkeypatch)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend))
    assert agent["n"] == 2
    assert grader["n"] == 1  # only the genuine attempt is graded
    assert result["check_verdict"] == "FAIL"
    assert result["termination_reason"] == TerminationReason.OK
    assert result["infra_retries"] == 1
    assert result["infra_retry_reasons"] == ["Error: Failed to load models"]
    assert len(sleeps) == 1 and sleeps[0] >= 15  # first backoff step (plus jitter)
    # Failed attempt's evidence is stashed; the retry metadata reaches disk.
    out = tmp_path / "out" / "Foo" / "Bar"
    assert "Failed to load models" in (out / "agent" / "attempts" / "attempt-0" / "stderr.txt").read_text()
    saved = json.loads((out / "result.json").read_text())
    assert saved["infra_retries"] == 1


def test_retry_exhaustion_is_error_not_fail(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [STARTUP] * 3)
    grader = _install_grader(monkeypatch)
    _no_sleep(monkeypatch)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, infra_retries=2))
    assert agent["n"] == 3
    assert grader["n"] == 0  # never grade a run the model never attempted
    assert result["check_verdict"] == "ERROR"
    assert result["termination_reason"] == TerminationReason.INFRA_ERROR
    assert result["infra_retries"] == 2
    assert result["infra_retry_reasons"] == ["Error: Failed to load models"] * 3
    assert "exhausted infra retries" in result["error"]


def test_genuine_attempt_never_retried(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [GENUINE_FAIL])
    grader = _install_grader(monkeypatch)
    sleeps = _no_sleep(monkeypatch)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend))
    assert agent["n"] == 1 and grader["n"] == 1
    assert result["check_verdict"] == "FAIL"
    assert "infra_retries" not in result
    assert sleeps == []


def test_midrun_infra_with_tokens_not_retried(tmp_path, monkeypatch):
    # INFRA_ERROR but the model DID work (tokens > 0): classified for downstream
    # filtering, but never re-run — the attempt was genuine.
    cut_off = {"exit": 1, "events": [{"type": "assistant.message", "data": {"content": "working"}}], "out_tokens": 42}
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [cut_off])
    grader = _install_grader(monkeypatch)
    _no_sleep(monkeypatch)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend))
    assert agent["n"] == 1 and grader["n"] == 1
    assert result["termination_reason"] == TerminationReason.INFRA_ERROR
    assert "infra_retries" not in result


def test_wall_clock_timeout_not_retried(tmp_path, monkeypatch):
    backend = _ScriptedBackend()
    timeout = {"exit": -1, "error": "copilot timeout after 10s"}
    agent = _install_agent(monkeypatch, backend, [timeout])
    grader = _install_grader(monkeypatch)
    sleeps = _no_sleep(monkeypatch)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend))
    assert agent["n"] == 1 and grader["n"] == 1
    assert result["termination_reason"] == TerminationReason.TIMEOUT
    assert sleeps == []


def test_infra_retries_zero_disables_retrying(tmp_path, monkeypatch):
    # 0 = no retries, but the no-attempt run still ends ERROR, never a proof FAIL.
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [STARTUP])
    grader = _install_grader(monkeypatch)
    sleeps = _no_sleep(monkeypatch)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend, infra_retries=0))
    assert agent["n"] == 1 and grader["n"] == 0
    assert result["check_verdict"] == "ERROR"
    assert result["termination_reason"] == TerminationReason.INFRA_ERROR
    assert result["infra_retries"] == 0
    assert sleeps == []


def test_retry_runs_on_fresh_workspace(tmp_path, monkeypatch):
    # A failed attempt's partial edits must not leak into the retry: attempt 1
    # scribbles on the benchmark, attempt 2 must see a pristine copy.
    seen = []

    def scribble(workspace):
        path = os.path.join(workspace, "Bar.tla")
        with open(path) as f:
            seen.append(f.read())
        with open(path, "w") as f:
            f.write("TAMPERED")

    def check(workspace):
        with open(os.path.join(workspace, "Bar.tla")) as f:
            seen.append(f.read())

    backend = _ScriptedBackend()
    attempts = [dict(STARTUP, mutate=scribble), dict(GENUINE_FAIL, mutate=check)]
    agent = _install_agent(monkeypatch, backend, attempts)
    _install_grader(monkeypatch)
    _no_sleep(monkeypatch)
    runner.run_single_benchmark(_work_item(tmp_path, backend))
    assert agent["workspaces"][0] != agent["workspaces"][1]
    assert seen == [BENCH_TEXT, BENCH_TEXT]


def test_retry_runs_on_fresh_canonical_snapshot(tmp_path, monkeypatch):
    # In local mode the agent can write to TLAPS_BENCHMARK_DIR. A failed
    # attempt's canonical snapshot must not leak into the retry or grader.
    seen = []

    def taint(canonical_dir):
        path = os.path.join(canonical_dir, "Bar.tla")
        with open(path) as f:
            seen.append(f.read())
        with open(path, "w") as f:
            f.write("TAINTED")

    def check(canonical_dir):
        with open(os.path.join(canonical_dir, "Bar.tla")) as f:
            seen.append(f.read())

    backend = _ScriptedBackend()
    attempts = [dict(STARTUP, mutate_canonical=taint), dict(GENUINE_FAIL, mutate_canonical=check)]
    agent = _install_agent(monkeypatch, backend, attempts)
    grader = _install_grader(monkeypatch, inspect_canonical=check)
    _no_sleep(monkeypatch)

    runner.run_single_benchmark(_work_item(tmp_path, backend))

    assert agent["canonical_dirs"][0] != agent["canonical_dirs"][1]
    assert grader["canonical_dirs"] == [agent["canonical_dirs"][1]]
    assert seen == [BENCH_TEXT, BENCH_TEXT, BENCH_TEXT]


def test_quota_exhaustion_is_not_infra_retried(tmp_path, monkeypatch):
    # Quota owns its own retry budget: once it reports exhaustion the infra loop
    # must stop dead — no reclassification, no extra attempts.
    backend = _ScriptedBackend()
    agent = _install_agent(monkeypatch, backend, [STARTUP] * 4)
    grader = _install_grader(monkeypatch)
    _no_sleep(monkeypatch)
    monkeypatch.setattr(runner.quota, "run_with_quota_retry", lambda run, block, **k: False)
    result = runner.run_single_benchmark(_work_item(tmp_path, backend))
    assert agent["n"] == 0  # the quota stub swallowed the run entirely
    assert grader["n"] == 0
    assert result["check_verdict"] == "ERROR"
    assert result["termination_reason"] == TerminationReason.QUOTA_EXHAUSTED
    assert "infra_retries" not in result


def test_quota_retry_clears_stale_stderr_before_final_run(tmp_path, monkeypatch):
    # quota.run_with_quota_retry can invoke the agent multiple times inside one
    # infra attempt. Stderr from the quota-blocked run must not label the final run.
    backend = _ScriptedBackend()
    blocks = iter([1, None])
    monkeypatch.setattr(backend, "detect_quota_block", lambda _jsonl: next(blocks))
    agent = _install_agent(monkeypatch, backend, [{"exit": 1, "stderr": "old quota/stderr noise\n"}, {"exit": 1}])
    grader = _install_grader(monkeypatch)
    _no_sleep(monkeypatch)

    result = runner.run_single_benchmark(_work_item(tmp_path, backend, infra_retries=0))

    assert agent["n"] == 2
    assert grader["n"] == 0
    assert result["check_verdict"] == "ERROR"
    assert result["termination_reason"] == TerminationReason.INFRA_ERROR
    assert result["infra_retry_reasons"] == ["no stderr"]
    assert not (tmp_path / "out" / "Foo" / "Bar" / "agent" / "stderr.txt").exists()
