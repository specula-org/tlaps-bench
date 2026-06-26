"""Integration tests that run check and validate inside Docker.

These require Docker and the tlaps-bench-base image.
Skip automatically if Docker is unavailable.

Run: uv run python -m pytest tests/common/test_docker_integration.py -v
"""

import os
import subprocess
import sys

import pytest

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
        tla = os.path.join(
            REPO_ROOT, "benchmark", "level1", "tlaplus_examples_allocator", "SimpleAllocator_proof_TypeCorrect.tla"
        )
        result = subprocess.run(
            ["uv", "run", "tlaps-bench", "check", tla, "--timeout", "120"],
            capture_output=True,
            text=True,
            timeout=180,
            cwd=REPO_ROOT,
        )
        # PROOF OBVIOUS = incomplete proof → should fail
        assert result.returncode == 1
        assert "FAIL" in result.stdout

    def test_check_sany_only_passes(self):
        """--sany-only on a valid .tla should PASS (parseable)."""
        tla = os.path.join(
            REPO_ROOT, "benchmark", "level1", "tlaplus_examples_allocator", "SimpleAllocator_proof_TypeCorrect.tla"
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
