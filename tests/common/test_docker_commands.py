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
            mode = "proof-completion"
            timeout = 60
            output = None
            benchmark_dir = None
            sany_only = False
            no_cache = False
            keep_verifying = False
            shards = None
            no_git_track = False

        with pytest.raises(SystemExit) as exc_info:
            _run_in_container(FIXTURE_TLA, Args())

        mock_run.assert_called_once()
        config, cmd = mock_run.call_args[0][:2]
        assert config.image.startswith("tlaps-bench-base:")
        assert config.image != "tlaps-bench-base:latest"
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
            mode = "proof-completion"
            timeout = 60
            output = None
            benchmark_dir = None
            sany_only = True
            no_cache = False
            keep_verifying = False
            shards = None
            no_git_track = False

        with pytest.raises(SystemExit):
            _run_in_container(FIXTURE_TLA, Args())

        cmd = mock_run.call_args[0][1]
        assert "--sany-only" in cmd

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_benchmark_dir_mounted_read_only_not_rewritten(self, mock_exists, mock_run):
        # The canonical baseline must be mounted at /benchmark, never rewritten
        # to the workspace: that would make the tamper oracle the solution itself.
        mock_run.return_value = (0, "✅ PASS\n", "")

        from common.check_proof import _run_in_container

        class Args:
            mode = "proof-completion"
            timeout = 60
            output = None
            benchmark_dir = "/host/canonical/Euclid"
            sany_only = False
            no_cache = False
            keep_verifying = False
            shards = None
            no_git_track = False

        with pytest.raises(SystemExit):
            _run_in_container(FIXTURE_TLA, Args())

        config, cmd = mock_run.call_args[0][0], mock_run.call_args[0][1]
        assert cmd[cmd.index("--benchmark-dir") + 1] == "/benchmark"
        assert config.benchmark_dir == "/host/canonical/Euclid"

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_no_cache_flag_passed(self, mock_exists, mock_run):
        mock_run.return_value = (0, "✅ PASS\n", "")

        from common.check_proof import _run_in_container

        class Args:
            mode = "proof-completion"
            timeout = 60
            output = None
            benchmark_dir = None
            sany_only = False
            no_cache = True
            keep_verifying = False
            shards = None
            no_git_track = False

        with pytest.raises(SystemExit):
            _run_in_container(FIXTURE_TLA, Args())

        cmd = mock_run.call_args[0][1]
        assert "--no-cache" in cmd

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_keep_verifying_no_git_track_and_shards_passed(self, mock_exists, mock_run):
        mock_run.return_value = (1, "❌ FAIL\n", "")

        from common.check_proof import _run_in_container

        class Args:
            mode = "proof-completion"
            timeout = 60
            output = None
            benchmark_dir = None
            sany_only = False
            no_cache = False
            keep_verifying = True
            no_git_track = True
            shards = 3

        with pytest.raises(SystemExit):
            _run_in_container(FIXTURE_TLA, Args())

        cmd = mock_run.call_args[0][1]
        assert "--keep-verifying" in cmd
        assert "--no-git-track" in cmd
        assert "--shards" in cmd and "3" in cmd

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_proof_from_scratch_passed(self, mock_exists, mock_run):
        mock_run.return_value = (0, "✅ PASS\n", "")

        from common.check_proof import _run_in_container

        class Args:
            mode = "proof-from-scratch"
            timeout = 60
            output = None
            benchmark_dir = None
            sany_only = False
            no_cache = False
            keep_verifying = False
            shards = None
            no_git_track = False

        with pytest.raises(SystemExit):
            _run_in_container(FIXTURE_TLA, Args())

        cmd = mock_run.call_args[0][1]
        assert "--mode" in cmd
        assert "proof-from-scratch" in cmd


class TestValidateDockerDispatch:
    """validate's run_tlapm_docker mounts workspace and calls tlapm."""

    @patch("common.container.ContainerRunner.run_with_output")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_run_tlapm_docker_calls_container(self, mock_exists, mock_run):
        mock_run.return_value = (0, "All 3 obligations proved.\n", "")

        from common.validate import run_tlapm_docker

        exit_code, output, elapsed = run_tlapm_docker(
            FIXTURE_TLA,
            timeout=60,
            container_image="tlaps-bench-base:immutable",
        )

        mock_run.assert_called_once()
        config, cmd = mock_run.call_args[0][:2]
        assert config.image == "tlaps-bench-base:immutable"
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

    @patch("common.container.ContainerRunner.require_docker")
    @patch("common.container.ContainerRunner.build_image")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_skips_build_when_exists(self, mock_exists, mock_build, mock_require):
        from common.container import ensure_image

        ensure_image()
        mock_require.assert_called_once()
        mock_build.assert_not_called()

    @patch("common.container.ContainerRunner.require_docker")
    @patch("common.container.ContainerRunner.build_image")
    @patch("common.container.ContainerRunner.image_exists", return_value=False)
    def test_builds_when_missing(self, mock_exists, mock_build, mock_require):
        from common.container import ensure_image

        ensure_image()
        mock_require.assert_called_once()
        mock_build.assert_called_once()

    @patch("common.container.ContainerRunner.require_docker")
    @patch("common.container.ContainerRunner.build_image")
    @patch("common.container.ContainerRunner.image_exists", return_value=True)
    def test_force_build_rebuilds(self, mock_exists, mock_build, mock_require):
        from common.container import ensure_image

        ensure_image(force=True)
        mock_require.assert_called_once()
        mock_build.assert_called_once()

    def test_stale_image_rebuilds_with_current_source_fingerprint(self):
        from common.container import IMAGE_TAG, ContainerRunner, ensure_image

        with (
            patch("common.container._image_source_fingerprint", return_value="source-sha256"),
            patch("common.container._checker_version", return_value="version"),
            patch("common.container._image_build_fingerprint", return_value="build-sha256"),
            patch.object(ContainerRunner, "require_docker") as mock_require,
            patch.object(ContainerRunner, "image_exists", return_value=False) as mock_exists,
            patch.object(ContainerRunner, "build_image") as mock_build,
        ):
            selected_image = ensure_image()

        mock_require.assert_called_once()
        expected_tag = f"{IMAGE_TAG}:build-sha256"
        assert selected_image == expected_tag
        mock_exists.assert_called_once_with(expected_tag, "build-sha256")
        assert mock_build.call_args.args[:3] == (
            os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))), "docker", "base.Dockerfile"),
            expected_tag,
            os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
        )
        assert mock_build.call_args.args[3] == {
            "CHECKER_VERSION": "version",
            "TLAPS_BENCH_BUILD_SHA256": "build-sha256",
        }
        assert mock_build.call_args.args[4] == [f"{IMAGE_TAG}:latest"]

    def test_cache_hit_restores_latest_alias_after_switching_sources(self):
        from common.container import IMAGE_TAG, ContainerRunner, ensure_image

        images = {}

        def image_exists(tag, build_sha256=None):
            return tag in images and (build_sha256 is None or images[tag] == build_sha256)

        def build_image(dockerfile, tag, context, build_args, additional_tags):
            del dockerfile, context
            build_sha256 = build_args["TLAPS_BENCH_BUILD_SHA256"]
            images[tag] = build_sha256
            for additional_tag in additional_tags:
                images[additional_tag] = build_sha256

        def tag_image(source_tag, target_tag):
            images[target_tag] = images[source_tag]

        with (
            patch("common.container._image_source_fingerprint", side_effect=["source-a", "source-b", "source-a"]),
            patch("common.container._checker_version", return_value="version"),
            patch("common.container._image_build_fingerprint", side_effect=["build-a", "build-b", "build-a"]),
            patch.object(ContainerRunner, "require_docker"),
            patch.object(ContainerRunner, "image_exists", side_effect=image_exists),
            patch.object(ContainerRunner, "build_image", side_effect=build_image) as mock_build,
            patch.object(ContainerRunner, "tag_image", side_effect=tag_image) as mock_tag,
        ):
            image_a = ensure_image()
            image_b = ensure_image()
            image_a_again = ensure_image()

        assert image_a == image_a_again == f"{IMAGE_TAG}:build-a"
        assert image_b == f"{IMAGE_TAG}:build-b"
        assert mock_build.call_count == 2
        mock_tag.assert_called_once_with(image_a, f"{IMAGE_TAG}:latest")
        assert images[f"{IMAGE_TAG}:latest"] == "build-a"


def test_image_source_fingerprint_tracks_runner_content_not_generated_files(tmp_path):
    from common.container import _image_source_fingerprint

    runner = tmp_path / "src" / "evaluator" / "backends" / "oneshot_runner.py"
    runner.parent.mkdir(parents=True)
    runner.write_text("first\n")
    (tmp_path / "docker").mkdir()
    (tmp_path / "docker" / "base.Dockerfile").write_text("FROM scratch\n")
    (tmp_path / ".dockerignore").write_text("**/*.pyc\n")
    (tmp_path / "pyproject.toml").write_text("[project]\n")

    initial = _image_source_fingerprint(str(tmp_path))
    os.utime(runner, None)
    assert _image_source_fingerprint(str(tmp_path)) == initial

    generated = tmp_path / "src" / "common" / "_build_version.py"
    generated.parent.mkdir(parents=True)
    generated.write_text('BUILD_VERSION = "dirty"\n')
    assert _image_source_fingerprint(str(tmp_path)) == initial

    ignored_result = runner.with_suffix(".result")
    ignored_result.write_text("temporary\n")
    assert _image_source_fingerprint(str(tmp_path)) == initial

    runner.write_text("second\n")
    assert _image_source_fingerprint(str(tmp_path)) != initial


def test_image_source_fingerprint_has_unambiguous_file_boundaries(tmp_path):
    from common.container import _image_source_fingerprint

    normal = tmp_path / "normal"
    corrupt = tmp_path / "corrupt"
    runner_relative = "src/evaluator/backends/oneshot_runner.py"
    next_relative = "src/evaluator/backends/pi.py"

    for root in (normal, corrupt):
        runner = root / runner_relative
        next_file = root / next_relative
        runner.parent.mkdir(parents=True)
        runner.write_bytes(b"runner content\n")
        next_file.write_bytes(b"next file content\n")

    corrupt_runner = corrupt / runner_relative
    corrupt_next = corrupt / next_relative
    next_mode = f"{corrupt_next.stat().st_mode & 0o777:o}".encode("ascii")
    embedded_next_record = (
        b"\0" + next_relative.encode("utf-8") + b"\0" + next_mode + b"\0file\0" + corrupt_next.read_bytes()
    )
    corrupt_runner.write_bytes(corrupt_runner.read_bytes() + embedded_next_record)
    corrupt_next.unlink()

    assert b"\0" in corrupt_runner.read_bytes()
    assert _image_source_fingerprint(str(normal)) != _image_source_fingerprint(str(corrupt))


def test_image_build_fingerprint_tracks_checker_version():
    from common.container import _image_build_fingerprint

    assert _image_build_fingerprint("same-source", "commit-a") != _image_build_fingerprint("same-source", "commit-b")


@patch("common.container.subprocess.run")
def test_build_image_applies_compatibility_alias(mock_run):
    from common.container import ContainerRunner

    mock_run.return_value = type("Result", (), {"returncode": 0})()
    ContainerRunner.build_image(
        "Dockerfile",
        "tlaps-bench-base:immutable",
        "/context",
        {"ARG": "value"},
        ["tlaps-bench-base:latest"],
    )

    assert mock_run.call_args.args[0] == [
        "docker",
        "build",
        "--platform",
        "linux/amd64",
        "-f",
        "Dockerfile",
        "-t",
        "tlaps-bench-base:immutable",
        "-t",
        "tlaps-bench-base:latest",
        "--build-arg",
        "ARG=value",
        "/context",
    ]


@patch("common.container.subprocess.run")
def test_image_build_label_must_match(mock_run):
    from common.container import ContainerRunner

    mock_run.return_value = type("Result", (), {"returncode": 0, "stdout": "current\n"})()

    assert ContainerRunner.image_exists("tlaps-bench-base", "current") is True
    assert ContainerRunner.image_exists("tlaps-bench-base", "stale") is False
    mock_run.return_value.stdout = "\n"
    assert ContainerRunner.image_exists("tlaps-bench-base", "current") is False

    inspect = mock_run.call_args_list[0].args[0]
    assert inspect == [
        "docker",
        "image",
        "inspect",
        "--format",
        '{{ index .Config.Labels "org.specula.tlaps-bench.build-sha256" }}',
        "tlaps-bench-base",
    ]


class TestDockerAvailability:
    @pytest.fixture(autouse=True)
    def _uncached(self):
        """require_docker memoizes success; start each test from a cold cache."""
        import common.container as container

        container._docker_ok = False
        yield
        container._docker_ok = False

    @patch("common.container.subprocess.run", side_effect=FileNotFoundError)
    def test_missing_cli_has_actionable_error(self, mock_run):
        from common.container import ContainerRunner, DockerUnavailableError

        with pytest.raises(DockerUnavailableError, match="Docker CLI not found"):
            ContainerRunner.require_docker()

    @patch("common.container.subprocess.run")
    def test_stopped_daemon_has_actionable_error(self, mock_run):
        from common.container import ContainerRunner, DockerUnavailableError

        mock_run.return_value = type("Result", (), {"returncode": 1, "stdout": "", "stderr": "daemon stopped"})()
        with pytest.raises(DockerUnavailableError, match="Docker daemon is unavailable"):
            ContainerRunner.require_docker()

    @patch("common.container.subprocess.run")
    def test_probe_runs_once_across_calls(self, mock_run):
        """Every container entry goes through ensure_image; don't re-probe per task."""
        from common.container import ContainerRunner

        mock_run.return_value = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()
        ContainerRunner.require_docker()
        ContainerRunner.require_docker()

        mock_run.assert_called_once()

    @patch("common.container.subprocess.run")
    def test_failure_is_not_cached(self, mock_run):
        """A stopped daemon that gets started must be picked up on the next call."""
        from common.container import ContainerRunner, DockerUnavailableError

        stopped = type("Result", (), {"returncode": 1, "stdout": "", "stderr": "daemon stopped"})()
        started = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()
        mock_run.side_effect = [stopped, started]

        with pytest.raises(DockerUnavailableError):
            ContainerRunner.require_docker()
        ContainerRunner.require_docker()

        assert mock_run.call_count == 2
