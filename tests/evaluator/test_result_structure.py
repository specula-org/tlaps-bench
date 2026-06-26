"""Tests for result directory structure."""

import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))


def make_result_dir() -> str:
    """Create a mock result directory with the expected structure."""
    base = tempfile.mkdtemp(prefix="tlaps_result_test_")

    # input/
    input_dir = os.path.join(base, "input")
    os.makedirs(input_dir)
    with open(os.path.join(input_dir, "benchmark.tla"), "w") as f:
        f.write("---- MODULE GCD ----\nTHEOREM GCD3 == TRUE\n  PROOF OBVIOUS\n====\n")
    with open(os.path.join(input_dir, "prompt.txt"), "w") as f:
        f.write("Write a proof for GCD3...")

    # agent/
    agent_dir = os.path.join(base, "agent")
    os.makedirs(agent_dir)
    with open(os.path.join(agent_dir, "output.jsonl"), "w") as f:
        f.write(json.dumps({"type": "response", "text": "proof"}) + "\n")
    with open(os.path.join(agent_dir, "stderr.txt"), "w") as f:
        f.write("")
    with open(os.path.join(agent_dir, "transcript.txt"), "w") as f:
        f.write("[AGENT] proof\n")
    with open(os.path.join(agent_dir, "solution.tla"), "w") as f:
        f.write("---- MODULE GCD ----\nTHEOREM GCD3 == TRUE\n  PROOF BY DEF GCD\n====\n")

    # grading/
    grading_dir = os.path.join(base, "grading")
    os.makedirs(grading_dir)
    with open(os.path.join(grading_dir, "check.result"), "w") as f:
        f.write("PASS\n")
    with open(os.path.join(grading_dir, "check_debug.txt"), "w") as f:
        f.write("exit code: 0\nAll 5 obligations proved.\n")

    # result.json
    with open(os.path.join(base, "result.json"), "w") as f:
        json.dump(
            {
                "benchmark": "Euclid/GCD_GCD3.tla",
                "backend": "litellm",
                "model": "gpt-5.5",
                "level": "level1",
                "verdict": "PASS",
                "time_secs": 42,
                "input_tokens": 1200,
                "output_tokens": 800,
                "obligations": 5,
                "sany_valid": True,
            },
            f,
        )

    return base


class TestResultStructure:
    def test_directories_exist(self):
        base = make_result_dir()
        try:
            assert os.path.isdir(os.path.join(base, "input"))
            assert os.path.isdir(os.path.join(base, "agent"))
            assert os.path.isdir(os.path.join(base, "grading"))
        finally:
            import shutil

            shutil.rmtree(base)

    def test_input_files(self):
        base = make_result_dir()
        try:
            assert os.path.isfile(os.path.join(base, "input", "benchmark.tla"))
            assert os.path.isfile(os.path.join(base, "input", "prompt.txt"))
        finally:
            import shutil

            shutil.rmtree(base)

    def test_agent_files(self):
        base = make_result_dir()
        try:
            agent_dir = os.path.join(base, "agent")
            assert os.path.isfile(os.path.join(agent_dir, "output.jsonl"))
            assert os.path.isfile(os.path.join(agent_dir, "transcript.txt"))
            assert os.path.isfile(os.path.join(agent_dir, "solution.tla"))
        finally:
            import shutil

            shutil.rmtree(base)

    def test_grading_files(self):
        base = make_result_dir()
        try:
            grading_dir = os.path.join(base, "grading")
            assert os.path.isfile(os.path.join(grading_dir, "check.result"))
            assert os.path.isfile(os.path.join(grading_dir, "check_debug.txt"))
        finally:
            import shutil

            shutil.rmtree(base)

    def test_result_json(self):
        base = make_result_dir()
        try:
            result_path = os.path.join(base, "result.json")
            assert os.path.isfile(result_path)
            with open(result_path) as f:
                data = json.load(f)
            assert data["benchmark"] == "Euclid/GCD_GCD3.tla"
            assert data["verdict"] == "PASS"
            assert data["time_secs"] == 42
            assert data["input_tokens"] == 1200
            assert data["output_tokens"] == 800
            assert data["obligations"] == 5
            assert data["sany_valid"] is True
        finally:
            import shutil

            shutil.rmtree(base)

    def test_no_stray_files_in_root(self):
        """Only result.json and the three subdirs should be at root level."""
        base = make_result_dir()
        try:
            entries = os.listdir(base)
            assert set(entries) == {"input", "agent", "grading", "result.json"}
        finally:
            import shutil

            shutil.rmtree(base)
