"""Integration tests that run check and validate inside Docker.

These require Docker and the tlaps-bench-base image.
Skip automatically if Docker is unavailable.

Run: uv run python -m pytest tests/common/test_docker_integration.py -v
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

from common.container import ContainerConfig, ContainerRunner

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

requires_docker = pytest.mark.skipif(
    subprocess.run(["docker", "info"], capture_output=True).returncode != 0,
    reason="Docker not available",
)
requires_image = pytest.mark.skipif(
    subprocess.run(["docker", "image", "inspect", "tlaps-bench-base:latest"], capture_output=True).returncode != 0,
    reason="tlaps-bench-base image not built",
)


@requires_docker
@requires_image
class TestCheckInDocker:
    """Run tlaps-bench check inside Docker against real benchmark files."""

    def test_check_proof_obvious_fails(self):
        """A benchmark with PROOF OBVIOUS should FAIL (proof not written)."""
        canonical_tla = os.path.join(
            REPO_ROOT,
            "benchmark",
            "proof-completion",
            "tlaplus_examples_allocator",
            "SimpleAllocator_proof_TypeCorrect.tla",
        )
        with tempfile.TemporaryDirectory(prefix="marked_submission_") as workspace:
            submission = Path(workspace) / os.path.basename(canonical_tla)
            submission.write_bytes(Path(canonical_tla).read_bytes())
            result = subprocess.run(
                [
                    "uv",
                    "run",
                    "tlaps-bench",
                    "check",
                    "--container",
                    "--benchmark-dir",
                    os.path.dirname(canonical_tla),
                    str(submission),
                    "--timeout",
                    "120",
                ],
                capture_output=True,
                text=True,
                timeout=180,
                cwd=REPO_ROOT,
            )
        # PROOF OBVIOUS = incomplete proof → should fail
        assert result.returncode == 1
        assert "FAIL" in result.stdout

    def test_full_check_rejects_self_canonical_target(self):
        tla = os.path.join(
            REPO_ROOT,
            "benchmark",
            "proof-completion",
            "tlaplus_examples_allocator",
            "SimpleAllocator_proof_TypeCorrect.tla",
        )
        result = subprocess.run(
            [
                "uv",
                "run",
                "tlaps-bench",
                "check",
                "--container",
                "--benchmark-dir",
                os.path.dirname(tla),
                tla,
                "--timeout",
                "120",
            ],
            capture_output=True,
            text=True,
            timeout=180,
            cwd=REPO_ROOT,
        )

        assert result.returncode == 3
        assert "canonical benchmark target must be independent" in result.stdout

    def test_container_checker_rejects_bind_mount_self_canonical_target(self):
        benchmark_dir = os.path.join(
            REPO_ROOT,
            "benchmark",
            "proof-completion",
            "tlaplus_examples_allocator",
        )
        basename = "SimpleAllocator_proof_TypeCorrect.tla"
        with tempfile.TemporaryDirectory(prefix="self_canonical_res_") as result_dir:
            config = ContainerConfig(
                image="tlaps-bench-base:latest",
                workspace=benchmark_dir,
                benchmark_dir=benchmark_dir,
                result_dir=result_dir,
            )
            exit_code, stdout, _stderr = ContainerRunner().run_with_output(
                config,
                [
                    "/usr/local/bin/check_proof_bin",
                    f"/workspace/{basename}",
                    "--no-container",
                    "--no-git-track",
                    "--benchmark-dir",
                    "/benchmark",
                    "--canonical-replay-required",
                    "--output",
                    "/results/check.result",
                ],
                timeout=120,
            )

        assert exit_code == 3
        assert "canonical benchmark target must be independent" in stdout

    def test_check_sany_only_passes(self):
        """--sany-only on a valid .tla should PASS (parseable)."""
        tla = os.path.join(
            REPO_ROOT,
            "benchmark",
            "proof-completion",
            "tlaplus_examples_allocator",
            "SimpleAllocator_proof_TypeCorrect.tla",
        )
        result = subprocess.run(
            ["uv", "run", "tlaps-bench", "check", "--sany-only", tla],
            capture_output=True,
            text=True,
            timeout=120,
            cwd=REPO_ROOT,
        )
        assert result.returncode == 0
        assert "SANY OK" in result.stdout

    def test_check_sany_only_rejects_duplicate_record_fields(self):
        with tempfile.TemporaryDirectory(prefix="sany_invalid_") as workspace:
            source = Path(workspace) / "Foo.tla"
            output = Path(workspace) / "duplicate.result"
            source.write_text(
                "---- MODULE Foo -----\n"
                "THEOREM False == ASSUME NEW r, r = [a |-> 1, a |-> 2] PROVE FALSE OBVIOUS\n"
                "=====\n"
            )
            result = subprocess.run(
                [
                    "uv",
                    "run",
                    "tlaps-bench",
                    "check",
                    "--container",
                    "--sany-only",
                    "--output",
                    str(output),
                    str(source),
                ],
                capture_output=True,
                text=True,
                timeout=120,
                cwd=REPO_ROOT,
            )
            sany_log = (Path(workspace) / "duplicate.sany.log").read_text()

        assert result.returncode == 1
        assert "SANY-STATUS: invalid" in result.stdout
        assert "[SANY-INVALID]" in result.stdout
        assert "status: invalid" in sany_log

    def test_check_sany_only_errors_when_tool_is_unavailable(self):
        with (
            tempfile.TemporaryDirectory(prefix="sany_unavailable_ws_") as workspace,
            tempfile.TemporaryDirectory(prefix="sany_unavailable_res_") as result_dir,
        ):
            (Path(workspace) / "Foo.tla").write_text("---- MODULE Foo ----\n====\n")
            config = ContainerConfig(
                image="tlaps-bench-base:latest",
                workspace=workspace,
                result_dir=result_dir,
                env={"SANY_RUN_SH": "/missing/run.sh"},
            )
            exit_code, stdout, _stderr = ContainerRunner().run_with_output(
                config,
                [
                    "/usr/local/bin/check_proof_bin",
                    "/workspace/Foo.tla",
                    "--no-container",
                    "--no-git-track",
                    "--sany-only",
                    "--output",
                    "/results/check.result",
                ],
                timeout=120,
            )
            sany_log = (Path(result_dir) / "sany.log").read_text()

        assert exit_code == 3
        assert "SANY-STATUS: unavailable" in stdout
        assert "status: unavailable" in sany_log


@requires_docker
@requires_image
class TestValidateInDocker:
    """Run tlaps-bench validate inside Docker against real benchmark files."""

    def test_validate_single_benchmark(self):
        """Validate a single known-good benchmark (source proof should verify)."""
        result = subprocess.run(
            [
                "uv",
                "run",
                "tlaps-bench",
                "validate",
                "--filter",
                "SimpleAllocator_proof_TypeCorrect",
                "--jobs",
                "1",
                "--timeout",
                "120",
            ],
            capture_output=True,
            text=True,
            timeout=240,
            cwd=REPO_ROOT,
        )
        # Should complete without crashing
        assert result.returncode == 0
        # Should report at least one benchmark processed
        assert "SimpleAllocator_proof_TypeCorrect" in result.stdout
