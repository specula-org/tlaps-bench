"""Programmatic Docker container interface for running agent backends."""

from __future__ import annotations

import contextlib
import os
import shlex
import subprocess
import time
import uuid
from dataclasses import dataclass, field
from pathlib import Path

# All provider API keys to auto-forward from host into containers.
# Sourced from litellm provider source code (llms/<provider>/).
API_KEY_VARS = [
    # OpenAI
    "OPENAI_API_KEY",
    "OPENAI_API_BASE",
    "OPENAI_BASE_URL",
    # DeepSeek
    "DEEPSEEK_API_KEY",
    "DEEPSEEK_API_BASE",
    # Anthropic
    "ANTHROPIC_API_KEY",
    "ANTHROPIC_API_BASE",
    # Gemini / Google
    "GOOGLE_API_KEY",
    "GEMINI_API_KEY",
    "GEMINI_API_BASE",
    # Azure OpenAI
    "AZURE_API_KEY",
    "AZURE_OPENAI_API_KEY",
    "AZURE_API_BASE",
    "AZURE_API_VERSION",
    "AZURE_OPENAI_HOST",
    "AZURE_AD_TOKEN",
    "AZURE_CLIENT_ID",
    "AZURE_CLIENT_SECRET",
    "AZURE_TENANT_ID",
    # AWS Bedrock
    "AWS_ACCESS_KEY_ID",
    "AWS_SECRET_ACCESS_KEY",
    "AWS_SESSION_TOKEN",
    "AWS_REGION_NAME",
    "AWS_REGION",
    "AWS_DEFAULT_REGION",
    "AWS_PROFILE",
    "AWS_ROLE_ARN",
    "AWS_WEB_IDENTITY_TOKEN_FILE",
    "AWS_BEDROCK_RUNTIME_ENDPOINT",
    # Vertex AI
    "VERTEXAI_PROJECT",
    "VERTEXAI_LOCATION",
    "VERTEX_LOCATION",
    "VERTEXAI_CREDENTIALS",
    "GOOGLE_APPLICATION_CREDENTIALS",
    # GitHub Copilot CLI
    "COPILOT_GITHUB_TOKEN",
    "COPILOT_PROVIDER_BASE_URL",
    "COPILOT_PROVIDER_API_KEY",
    "COPILOT_PROVIDER_TYPE",
    "GH_TOKEN",
    "GITHUB_TOKEN",
    # Claude Code OAuth
    "CLAUDE_CODE_OAUTH_TOKEN",
    # WatsonX / IBM
    "WATSONX_API_KEY",
    "WATSONX_URL",
    "WATSONX_PROJECT_ID",
    # Moonshot
    "MOONSHOT_API_KEY",
]


@dataclass
class ContainerConfig:
    """Configuration for a single container run."""

    image: str = "tlaps-bench-base:latest"
    workspace: str = ""  # host path, mounted to /workspace (rw)
    result_dir: str = ""  # host path, mounted to /results (rw)
    env: dict[str, str] = field(default_factory=dict)
    firewall_hosts: list[str] = field(default_factory=list)
    install_script: str | None = None  # run at container start before agent cmd
    cap_net_admin: bool = True
    memory: str = "8g"
    cpus: float = 4.0


@dataclass
class ContainerRun:
    """Handle for a running container."""

    proc: subprocess.Popen
    container_id: str


class ContainerRunner:
    """Programmatic interface to Docker for running agent backends in isolation."""

    def build_docker_args(self, config: ContainerConfig) -> tuple[list[str], str]:
        """Build the `docker run` argument list from config."""
        cid_file = f"/tmp/tlaps-bench-{uuid.uuid4().hex[:8]}.cid"

        args = [
            "docker",
            "run",
            "--rm",
            "--init",
            "-i",
            f"--cidfile={cid_file}",
            f"--cpus={config.cpus}",
            f"--memory={config.memory}",
        ]

        if config.cap_net_admin and config.firewall_hosts:
            args.append("--cap-add=NET_ADMIN")

        # Workspace and result mounts
        if config.workspace:
            args.extend(["-v", f"{config.workspace}:/workspace:rw"])
        if config.result_dir:
            args.extend(["-v", f"{config.result_dir}:/results:rw"])

        # tlapm from host (avoids re-download on image rebuild)
        tlapm_host = Path.home() / ".tlapm"
        if tlapm_host.is_dir():
            args.extend(["-v", f"{tlapm_host.resolve()}:/opt/tlapm:ro"])

        # Credential directory mounts (read-only except codex which needs write for cache)
        aws_dir = Path.home() / ".aws"
        if aws_dir.is_dir():
            args.extend(["-v", f"{aws_dir.resolve()}:/root/.aws:ro"])

        codex_dir = Path.home() / ".codex"
        if codex_dir.is_dir():
            args.extend(["-v", f"{codex_dir.resolve()}:/root/.codex"])

        copilot_dir = Path.home() / ".copilot"
        if copilot_dir.is_dir():
            args.extend(["-v", f"{copilot_dir.resolve()}:/root/.copilot"])

        # Env vars
        for key, value in config.env.items():
            args.extend(["-e", f"{key}={value}"])

        # Firewall hosts as env var (read by firewall.sh inside container)
        if config.firewall_hosts:
            args.extend(["-e", f"FIREWALL_HOSTS={','.join(config.firewall_hosts)}"])
        else:
            args.extend(["-e", "DISABLE_FIREWALL=1"])

        args.append(config.image)
        return args, cid_file

    def build_composite_command(self, cmd: list[str], install_script: str | None = None) -> str:
        """Build shell command: install script → firewall → agent command."""
        agent_cmd = " ".join(shlex.quote(c) for c in cmd)
        parts = []
        if install_script:
            parts.append(f"/opt/install-scripts/{install_script} >&2")
        parts.append("/opt/firewall.sh >&2 || true")
        parts.append(f"exec {agent_cmd}")
        return " && ".join(parts)

    def run(self, config: ContainerConfig, cmd: list[str], stdin_data: str | None = None) -> ContainerRun:
        """Launch a container with the given command. Returns handle."""
        docker_args, cid_file = self.build_docker_args(config)
        composite = self.build_composite_command(cmd, config.install_script)
        full_cmd = docker_args + ["bash", "-c", composite]

        proc = subprocess.Popen(
            full_cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )

        if stdin_data and proc.stdin:
            try:
                proc.stdin.write(stdin_data)
                proc.stdin.close()
            except BrokenPipeError:
                pass

        container_id = self._read_cidfile(cid_file)
        return ContainerRun(proc=proc, container_id=container_id)

    def run_with_output(
        self, config: ContainerConfig, cmd: list[str], stdin_data: str | None = None, timeout: int | None = None
    ) -> tuple[int, str, str]:
        """Run container to completion. Returns (exit_code, stdout, stderr)."""
        docker_args, cid_file = self.build_docker_args(config)
        composite = self.build_composite_command(cmd, config.install_script)
        full_cmd = docker_args + ["bash", "-c", composite]

        try:
            result = subprocess.run(
                full_cmd,
                input=stdin_data,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
            return result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired:
            cid = self._read_cidfile(cid_file)
            if cid:
                self.kill_by_id(cid)
            raise

    def kill(self, run: ContainerRun) -> None:
        """Kill a running container."""
        if run.container_id:
            self.kill_by_id(run.container_id)
        else:
            with contextlib.suppress(ProcessLookupError):
                run.proc.kill()

    def kill_by_id(self, container_id: str) -> None:
        """Kill a container by ID."""
        subprocess.run(
            ["docker", "kill", container_id],
            capture_output=True,
            timeout=10,
        )

    def wait(self, run: ContainerRun, timeout: int | None = None) -> int:
        """Wait for container to exit. Returns exit code."""
        try:
            run.proc.communicate(timeout=timeout)
            return run.proc.returncode
        except subprocess.TimeoutExpired:
            self.kill(run)
            run.proc.wait(timeout=10)
            raise

    @staticmethod
    def _read_cidfile(cid_file: str, retries: int = 10) -> str:
        """Read container ID from cidfile with retries."""
        for _ in range(retries):
            try:
                with open(cid_file) as f:
                    cid = f.read().strip()
                if cid:
                    os.unlink(cid_file)
                    return cid
            except FileNotFoundError:
                pass
            time.sleep(0.2)
        return ""

    @staticmethod
    def build_image(dockerfile: str, tag: str, context: str) -> None:
        """Build a Docker image, streaming output to stdout."""
        print(f"[build] docker build -t {tag}...")
        result = subprocess.run(
            ["docker", "build", "-f", dockerfile, "-t", tag, context],
        )
        if result.returncode != 0:
            raise RuntimeError(f"Docker build failed (exit {result.returncode})")

    @staticmethod
    def image_exists(tag: str) -> bool:
        """Check if a Docker image exists locally."""
        result = subprocess.run(
            ["docker", "image", "inspect", tag],
            capture_output=True,
        )
        return result.returncode == 0

    def run_preflight(
        self, config: ContainerConfig, backend_name: str, install_script: str | None = None
    ) -> None:
        """Run the backend's preflight check inside a container.

        Installs the CLI, then calls the backend's run_preflight() to validate
        model + credentials with a minimal API call. Fails fast on error.
        """
        check_cmd = (
            f"python3 -c "
            f"'from evaluator.backends.{backend_name} import run_preflight; run_preflight()'"
        )
        if install_script:
            check_cmd = f"/opt/install-scripts/{install_script} > /dev/null 2>&1 && {check_cmd}"

        docker_args, cid_file = self.build_docker_args(config)
        full_cmd = docker_args + ["bash", "-c", check_cmd]

        print(f"🔍 Running preflight check for '{backend_name}'...")
        result = subprocess.run(
            full_cmd,
            capture_output=True,
            text=True,
            timeout=180,
        )
        if result.returncode != 0:
            output = (result.stdout or result.stderr or "").strip()
            raise RuntimeError(
                f"❌ Preflight failed for '{backend_name}' (exit {result.returncode}):\n{output}"
            )
        print(f"✅ Preflight passed for '{backend_name}'")


def forward_env(backend_keys: list[str], model: str | None = None) -> dict[str, str]:
    """Build env dict for container: auto-forward all API keys + backend-specific vars + model."""
    env: dict[str, str] = {}

    # Auto-forward all known provider API keys from host
    for key in API_KEY_VARS:
        val = os.environ.get(key)
        if val:
            env[key] = val

    # Forward any backend-specific keys not in the global list
    for key in backend_keys:
        if key not in env:
            val = os.environ.get(key)
            if val:
                env[key] = val

    # Pass model ID so drivers/agents inside the container know which model to use
    if model:
        env["AGENT_MODEL_ID"] = model

    return env
