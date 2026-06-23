"""End-to-end integration test using a real LLM via ContainerRunner.

Tests the full pipeline: ContainerRunner → install litellm → call Claude → write proof → grade on host.
Requires: ANTHROPIC_API_KEY, Docker, tlaps-bench-base image, tlapm, check_proof_bin.

Usage:
    pytest tests/evaluator/test_llm_integration.py -v
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

from evaluator.backends.litellm import LiteLLMBackend
from evaluator.container import ContainerConfig, ContainerRunner, forward_env
from evaluator.levels import get_level

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
BENCHMARK_FILE = os.path.join(REPO_ROOT, "benchmark", "level1", "Euclid", "GCD_GCD3.tla")
CHECKER_BIN = os.path.join(REPO_ROOT, "check_proof_bin")
TLAPM_PATH = os.path.expanduser("~/.tlapm")
BASE_IMAGE = "tlaps-bench-base:latest"

requires_anthropic = pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY"),
    reason="ANTHROPIC_API_KEY not set",
)
requires_tlapm = pytest.mark.skipif(
    not os.path.isfile(os.path.join(TLAPM_PATH, "bin", "tlapm")),
    reason="tlapm not installed at ~/.tlapm",
)
requires_checker = pytest.mark.skipif(
    not os.path.isfile(CHECKER_BIN),
    reason="check_proof_bin not built (run `make`)",
)
requires_docker = pytest.mark.skipif(
    subprocess.run(["docker", "info"], capture_output=True).returncode != 0,
    reason="Docker not available",
)
requires_image = pytest.mark.skipif(
    subprocess.run(["docker", "image", "inspect", BASE_IMAGE], capture_output=True).returncode != 0,
    reason=f"Docker image {BASE_IMAGE} not built (run: docker build -f docker/base.Dockerfile -t {BASE_IMAGE} .)",
)


@requires_anthropic
@requires_docker
@requires_image
@requires_tlapm
@requires_checker
def test_container_litellm_e2e():
    """Full pipeline through Docker: install litellm → call Claude → grade."""
    backend = LiteLLMBackend(model="anthropic/claude-sonnet-4-6")
    level = get_level("level1", os.path.join(REPO_ROOT, "benchmark"), CHECKER_BIN)
    runner = ContainerRunner()

    basename = "GCD_GCD3.tla"
    workspace = tempfile.mkdtemp(prefix="test_container_e2e_")
    result_dir = tempfile.mkdtemp(prefix="test_container_e2e_results_")
    input_dir = os.path.join(result_dir, "input")
    agent_dir = os.path.join(result_dir, "agent")
    grading_dir = os.path.join(result_dir, "grading")
    for d in (input_dir, agent_dir, grading_dir):
        os.makedirs(d)

    try:
        # Setup workspace
        shutil.copy2(BENCHMARK_FILE, os.path.join(workspace, basename))
        for dep in level.get_dependencies(BENCHMARK_FILE):
            shutil.copy2(dep, os.path.join(workspace, os.path.basename(dep)))

        subprocess.run(["git", "init"], capture_output=True, cwd=workspace)
        subprocess.run(["git", "add", "."], capture_output=True, cwd=workspace)
        subprocess.run(
            ["git", "commit", "-m", "initial"],
            capture_output=True,
            cwd=workspace,
            env={
                **os.environ,
                "GIT_AUTHOR_NAME": "bench",
                "GIT_AUTHOR_EMAIL": "bench@bench",
                "GIT_COMMITTER_NAME": "bench",
                "GIT_COMMITTER_EMAIL": "bench@bench",
            },
        )

        # Build prompt
        tlapm_lib = None
        for sub in ["lib/tlapm/stdlib", "lib/tlaps", "lib/tlapm", "lib"]:
            path = os.path.join(TLAPM_PATH, sub)
            if os.path.isdir(path):
                tlapm_lib = path
                break
        assert tlapm_lib is not None, "tlapm lib not found"

        prompt = level.build_prompt(basename, TLAPM_PATH, tlapm_lib)

        # Save input artifacts
        shutil.copy2(BENCHMARK_FILE, os.path.join(input_dir, "benchmark.tla"))
        with open(os.path.join(input_dir, "prompt.txt"), "w") as f:
            f.write(prompt)

        # Run agent through ContainerRunner
        cmd = backend.build_command("/workspace", "/results")
        config = ContainerConfig(
            image=BASE_IMAGE,
            workspace=workspace,
            result_dir=result_dir,
            env=forward_env(backend.env_keys, model=backend.model),
            firewall_hosts=backend.firewall_hosts(),
            install_script=backend.install_script,
            user_id=os.getuid(),
            group_id=os.getgid(),
        )

        exit_code, stdout, stderr = runner.run_with_output(
            config, cmd, stdin_data=prompt, timeout=180
        )

        # Save agent output
        agent_jsonl = os.path.join(agent_dir, "output.jsonl")
        with open(agent_jsonl, "w") as f:
            f.write(stdout)
        if stderr:
            with open(os.path.join(agent_dir, "stderr.txt"), "w") as f:
                f.write(stderr)

        # Verify agent ran successfully
        assert exit_code == 0, f"Container agent failed (exit {exit_code}): {stderr}"
        assert os.path.getsize(agent_jsonl) > 0, "Agent produced no output"

        # Parse output
        transcript, in_tok, out_tok = backend.parse_output(agent_jsonl)
        assert in_tok > 0, "No input tokens recorded"
        assert out_tok > 0, "No output tokens recorded"

        # Verify solution was written to workspace (via mount)
        solution_path = os.path.join(workspace, basename)
        with open(solution_path) as f:
            solution_content = f.read()
        assert "PROOF OBVIOUS" not in solution_content, "Agent didn't modify the proof"
        assert "MODULE" in solution_content, "Solution doesn't looTLA+ file"
        shutil.copy2(solution_path, os.path.join(agent_dir, "solution.tla"))

        with open(os.path.join(agent_dir, "transcript.txt"), "w") as f:
            f.write(transcript)

        # Grade on host
        check_result_path = os.path.join(grading_dir, "check.result")
        check_cmd = level.checker_command(
            workspace, basename, check_result_path, 300,
            benchmark_dir=os.path.dirname(BENCHMARK_FILE),
        )
        check_env = dict(os.environ)
        sany_run_sh = os.path.join(REPO_ROOT, "src", "dataset", "sany-dump", "run.sh")
        if os.path.isfile(sany_run_sh):
            check_env["SANY_RUN_SH"] = sany_run_sh

        check_proc = subprocess.run(
            check_cmd,
            capture_output=True,
            text=True,
            timeout=360,
            cwd=workspace,
            env=check_env,
        )
        with open(os.path.join(grading_dir, "check_debug.txt"), "w") as f:
            f.write(f"exit code: {check_proc.returncode}\n")
            f.write(f"stdout:\n{check_proc.stdout}\n")
            f.write(f"stderr:\n{check_proc.stderr}\n")

        assert check_proc.returncode in (0, 1, 2), f"Unexpected checker exit: {check_proc.returncode}"
        verdict = {0: "PASS", 1: "FAIL", 2: "CHEATING"}[check_proc.returncode]

        # Write result.json
        result = {
            "benchmark": "Euclid/GCD_GCD3.tla",
            "backend": "litellm",
            "model": "anthropic/claude-sonnet-4-6",
            "level": "level1",
            "verdict": verdict,
            "input_tokens": in_tok,
            "output_tokens": out_tok,
        }
        with open(os.path.join(result_dir, "result.json"), "w") as f:
            json.dump(result, f, indent=2)

        # Verify directory structure
        assert os.path.isfile(os.path.join(input_dir, "benchmark.tla"))
        assert os.path.isfile(os.path.join(input_dir, "prompt.txt"))
        assert os.path.isfile(os.path.join(agent_dir, "output.jsonl"))
        assert os.path.isfile(os.path.join(agent_dir, "solution.tla"))
        assert os.path.isfile(os.path.join(agent_dir, "transcript.txt"))
        assert os.path.isfile(os.path.join(grading_dir, "check_debug.txt"))
        assert os.path.isfile(os.path.join(result_dir, "result.json"))

        print(f"\n  Verdict: {verdict}")
        print(f"  Tokens: {in_tok} in / {out_tok} out")
        print(f"  Checker: {check_proc.stdout[:200]}")

    finally:
        shutil.rmtree(workspace, ignore_errors=True)
        shutil.rmtree(result_dir, ignore_errors=True)


@requires_anthropic
def test_litellm_api_smoke():
    """Smoke test: verify the LLM API call works."""
    import litellm

    response = litellm.completion(
        model="anthropic/claude-sonnet-4-6",
        messages=[{"role": "user", "content": "Say 'ok'"}],
        max_tokens=10,
    )
    assert response.choices[0].message.content
    assert response.usage.prompt_tokens > 0
    assert response.usage.completion_tokens > 0
