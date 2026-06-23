"""Tests for ContainerRunner."""

import os
import sys
from unittest.mock import MagicMock, patch

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

from evaluator.container import ContainerConfig, ContainerRunner, forward_env


class TestBuildDockerArgs:
    def test_basic_args(self):
        runner = ContainerRunner()
        config = ContainerConfig(workspace="/tmp/ws", result_dir="/tmp/res", user_id=1000, group_id=1000)
        args, cid_file = runner.build_docker_args(config)

        assert args[0] == "docker"
        assert args[1] == "run"
        assert "--rm" in args
        assert "-i" in args
        assert "--memory=8g" in args
        assert "--cpus=4.0" in args
        assert "--user=1000:1000" in args

    def test_workspace_mount(self):
        runner = ContainerRunner()
        config = ContainerConfig(workspace="/tmp/ws")
        args, _ = runner.build_docker_args(config)

        assert "-v" in args
        idx = args.index("-v")
        assert args[idx + 1] == "/tmp/ws:/workspace:rw"

    def test_result_dir_mount(self):
        runner = ContainerRunner()
        config = ContainerConfig(result_dir="/tmp/res")
        args, _ = runner.build_docker_args(config)

        mount_args = [args[i + 1] for i, a in enumerate(args) if a == "-v"]
        assert "/tmp/res:/results:rw" in mount_args

    def test_env_forwarding(self):
        runner = ContainerRunner()
        config = ContainerConfig(env={"OPENAI_API_KEY": "sk-test", "FOO": "bar"})
        args, _ = runner.build_docker_args(config)

        env_args = [args[i + 1] for i, a in enumerate(args) if a == "-e"]
        assert "OPENAI_API_KEY=sk-test" in env_args
        assert "FOO=bar" in env_args

    def test_firewall_hosts_set(self):
        runner = ContainerRunner()
        config = ContainerConfig(firewall_hosts=["api.openai.com", "api.anthropic.com"])
        args, _ = runner.build_docker_args(config)

        assert "--cap-add=NET_ADMIN" in args
        env_args = [args[i + 1] for i, a in enumerate(args) if a == "-e"]
        assert "FIREWALL_HOSTS=api.openai.com,api.anthropic.com" in env_args

    def test_no_firewall_when_empty(self):
        runner = ContainerRunner()
        config = ContainerConfig(firewall_hosts=[])
        args, _ = runner.build_docker_args(config)

        assert "--cap-add=NET_ADMIN" not in args
        env_args = [args[i + 1] for i, a in enumerate(args) if a == "-e"]
        assert "DISABLE_FIREWALL=1" in env_args

    def test_image_at_end(self):
        runner = ContainerRunner()
        config = ContainerConfig(image="my-image:v1")
        args, _ = runner.build_docker_args(config)

        assert args[-1] == "my-image:v1"

    def test_no_user_when_zero(self):
        runner = ContainerRunner()
        config = ContainerConfig(user_id=0, group_id=0)
        args, _ = runner.build_docker_args(config)

        assert not any(a.startswith("--user=") for a in args)


class TestBuildCompositeCommand:
    def test_without_install_script(self):
        runner = ContainerRunner()
        result = runner.build_composite_command(["codex", "exec", "--model", "gpt-5.5"])
        assert result == "exec codex exec --model gpt-5.5"

    def test_with_install_script(self):
        runner = ContainerRunner()
        result = runner.build_composite_command(
            ["codex", "exec", "--model", "gpt-5.5"],
            install_script="install-codex.sh",
        )
        assert result == "/opt/install-scripts/install-codex.sh && exec codex exec --model gpt-5.5"

    def test_command_quoting(self):
        runner = ContainerRunner()
        result = runner.build_composite_command(["echo", "hello world"])
        assert "hello world" in result  # should be quoted


class TestForwardEnv:
    def test_forwards_set_vars(self):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-test", "FOO": "bar"}, clear=True):
            result = forward_env(["FOO"])
            assert result["OPENAI_API_KEY"] == "sk-test"  # auto-forwarded
            assert result["FOO"] == "bar"  # backend-specific

    def test_skips_empty(self):
        with patch.dict(os.environ, {"EMPTY_KEY": ""}, clear=True):
            result = forward_env(["EMPTY_KEY"])
            assert "EMPTY_KEY" not in result

    def test_empty_keys_list(self):
        with patch.dict(os.environ, {}, clear=True):
            result = forward_env([])
            assert result == {}

    def test_model_passed(self):
        with patch.dict(os.environ, {}, clear=True):
            result = forward_env([], model="gpt-5.5")
            assert result["AGENT_MODEL_ID"] == "gpt-5.5"

    def test_model_none_not_set(self):
        with patch.dict(os.environ, {}, clear=True):
            result = forward_env([])
            assert "AGENT_MODEL_ID" not in result


class TestKill:
    @patch("subprocess.run")
    def test_kill_by_id(self, mock_run):
        runner = ContainerRunner()
        runner.kill_by_id("abc123")
        mock_run.assert_called_once_with(
            ["docker", "kill", "abc123"],
            capture_output=True,
            timeout=10,
        )

    @patch("subprocess.run")
    def test_kill_container_run(self, mock_run):
        runner = ContainerRunner()
        proc = MagicMock()
        run = MagicMock(container_id="abc123", proc=proc)
        runner.kill(run)
        mock_run.assert_called_once_with(
            ["docker", "kill", "abc123"],
            capture_output=True,
            timeout=10,
        )

    def test_kill_fallback_no_container_id(self):
        runner = ContainerRunner()
        proc = MagicMock()
        run = MagicMock(container_id="", proc=proc)
        runner.kill(run)
        proc.kill.assert_called_once()
