"""Tests for check and validate Docker/local dispatch.

Mocks ContainerRunner.run_with_output so no Docker needed.

Run: uv run python -m pytest tests/common/test_docker_commands.py -v
"""

import os
import subprocess
import sys
from unittest.mock import patch

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

FIXTURE_DIR = os.path.join(os.path.dirname(__file__), "fixtures")
FIXTURE_TLA = os.path.join(FIXTURE_DIR, "Simple_TypeOK.tla")

FIXTURE_CONTENT = """\
---- MODULE Simple_TypeOK ----
EXTENDS Naturals, TLAPS
VARIABLE x
TypeOK == x \\in Nat
Init == x = 0
Next == x' = x + 1
Spec == Init /\\ [][Next]_x
THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS
====
"""


@pytest.fixture(autouse=True)
def fixture_file(tmp_path):
    """Create a minimal .tla fixture."""
    os.makedirs(FIXTURE_DIR, exist_ok=True)
    with open(FIXTURE_TLA, "w") as f:
        f.write(FIXTURE_CONTENT)
    yield
    if os.path.isfile(FIXTURE_TLA):
        os.remove(FIXTURE_TLA)
    if os.path.isdir(FIXTURE_DIR) and not os.listdir(FIXTURE_DIR):
        os.rmdir(FIXTURE_DIR)


class TestCheckDockerDispatch:
    """check defaults to Docker, --no-container uses local tlapm."""

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_default_runs_in_container(self, mock_exists, mock_run):
        mock_run.return_value = (1, "❌ FAIL\n", "")

        from common.check_proof import _run_in_container

        # Simulate args
        class Args:
            level = 1
            timeout = 60
            output = None
            benchmark_dir = None
            sany_only = False

        with pytest.raises(SystemExit) as exc_info:
            _run_in_container(FIXTURE_TLA, Args())

        mock_run.assert_called_once()
        config, cmd = mock_run.call_args[0][:2]
        # Mounts repo root (for git access) or fixture dir (no git)
        assert os.path.isdir(config.workspace)
        assert cmd[0] == "/usr/local/bin/check_proof_bin"
        # File path is relative to workspace
        assert any("Simple_TypeOK.tla" in c for c in cmd)
        assert exc_info.value.code == 1

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_sany_only_flag_passed(self, mock_exists, mock_run):
        mock_run.return_value = (0, "✅ SANY OK\n", "")

        from common.check_proof import _run_in_container

        class Args:
            level = 1
            timeout = 60
            output = None
            benchmark_dir = None
            sany_only = True

        with pytest.raises(SystemExit):
            _run_in_container(FIXTURE_TLA, Args())

        cmd = mock_run.call_args[0][1]
        assert "--sany-only" in cmd

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_level2_passed(self, mock_exists, mock_run):
        mock_run.return_value = (0, "✅ PASS\n", "")

        from common.check_proof import _run_in_container

        class Args:
            level = 2
            timeout = 60
            output = None
            benchmark_dir = None
            sany_only = False

        with pytest.raises(SystemExit):
            _run_in_container(FIXTURE_TLA, Args())

        cmd = mock_run.call_args[0][1]
        assert "--level" in cmd
        assert "2" in cmd


class TestValidateDockerDispatch:
    """validate's run_tlapm_docker mounts workspace and calls tlapm."""

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_run_tlapm_docker_calls_container(self, mock_exists, mock_run):
        mock_run.return_value = (0, "All 3 obligations proved.\n", "")

        from common.validate import run_tlapm_docker

        exit_code, output, elapsed = run_tlapm_docker(FIXTURE_TLA, timeout=60)

        mock_run.assert_called_once()
        config, cmd = mock_run.call_args[0][:2]
        assert config.workspace == FIXTURE_DIR
        assert cmd[0] == "/opt/tlapm/bin/tlapm"
        assert "--strict" in cmd
        assert "/workspace/Simple_TypeOK.tla" in cmd
        assert exit_code == 0
        assert "obligations proved" in output

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_run_tlapm_docker_timeout(self, mock_exists, mock_run):
        mock_run.side_effect = subprocess.TimeoutExpired(cmd="docker", timeout=60)

        from common.validate import run_tlapm_docker

        exit_code, output, elapsed = run_tlapm_docker(FIXTURE_TLA, timeout=60)

        assert exit_code == -1
        assert "TIMEOUT" in output

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_run_tlapm_docker_error(self, mock_exists, mock_run):
        mock_run.side_effect = RuntimeError("Docker daemon not running")

        from common.validate import run_tlapm_docker

        exit_code, output, elapsed = run_tlapm_docker(FIXTURE_TLA, timeout=60)

        assert exit_code == -2
        assert "Docker daemon" in output


class TestEnsureImage:
    """ensure_image builds only when needed."""

    @patch("common.container.ContainerRunner.build_image")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_skips_build_when_exists(self, mock_exists, mock_build):
        from common.container import ensure_image

        ensure_image()
        mock_build.assert_not_called()

    @patch("common.container.ContainerRunner.build_image")
    @patch("common.container.ContainerRunner.image_exists", return_value=False)
    def test_builds_when_missing(self, mock_exists, mock_build):
        from common.container import ensure_image

        ensure_image()
        mock_build.assert_called_once()

    @patch("common.container.ContainerRunner.build_image")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_force_build_rebuilds(self, mock_exists, mock_build):
        from common.container import ensure_image

        ensure_image(force=True)
        mock_build.assert_called_once()
