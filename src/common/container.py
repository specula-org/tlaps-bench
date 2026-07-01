"""Programmatic Docker container interface for running agent backends."""

from __future__ import annotations

import contextlib
import os
import shlex
import shutil
import subprocess
import tempfile
import time
import tomllib
import uuid
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path

IMAGE_TAG = "tlaps-bench-base"
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

# In-image location of the bundled agent skills (see docker/base.Dockerfile,
# which copies docs/skill here). Each agent CLI discovers skills from its own
# personal directory (~/.copilot/skills, ~/.claude/skills, ~/.codex/skills), so
# at container start we link those to _AGENT_SKILLS_DIR. Doing it at start (not
# in the image) makes it survive a credential mount that replaces ~/.<agent>:
# the command runs after mounts are in place, and writes into the mounted copy,
# never the host.
_AGENT_SKILLS_DIR = "/opt/agent-skills"
_AGENT_SKILL_HOMES = ("/root/.copilot", "/root/.claude", "/root/.codex")

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
    "AWS_BEARER_TOKEN_BEDROCK",
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
    benchmark_dir: str = ""  # host path, mounted to /benchmark (ro) for tamper-proof baseline
    env: dict[str, str] = field(default_factory=dict)
    firewall_hosts: list[str] = field(default_factory=list)
    install_script: str | None = None  # run at container start before agent cmd
    cap_net_admin: bool = True
    memory: str = ""
    cpus: float = 0
    credential_mounts: list[str] = field(default_factory=list)  # host credential dirs to copy+mount


@dataclass
class ContainerRun:
    """Handle for a running container."""

    proc: subprocess.Popen
    container_id: str


@dataclass(frozen=True)
class CredentialMount:
    """How to prepare and mount a host credential directory."""

    mount_path: str
    copy: Callable[[Path, Path], bool]


def _copy_all_credentials(src: Path, dst: Path) -> bool:
    """Copy a complete credential directory for providers with complex auth flows."""
    # AWS profile/SSO resolution can need several files; the container firewall
    # still keeps egress scoped to the configured model/API hosts.
    shutil.copytree(
        src,
        dst,
        dirs_exist_ok=True,
        symlinks=True,
        ignore_dangling_symlinks=True,
        copy_function=lambda s, d: shutil.copy2(s, d) if os.access(s, os.R_OK) else None,
    )
    return True


def _copy_named_credential_file(src: Path, dst: Path, filename: str) -> bool:
    """Copy one auth file, rejecting symlinks to avoid copying unrelated host files."""
    auth_src = src / filename
    if auth_src.is_symlink() or not auth_src.is_file() or not os.access(auth_src, os.R_OK):
        return False
    shutil.copy2(auth_src, dst / filename)
    return True


def _copy_claude_credentials(src: Path, dst: Path) -> bool:
    """Copy only Claude Code's OAuth credential file."""
    return _copy_named_credential_file(src, dst, ".credentials.json")


def _copy_copilot_credentials(src: Path, dst: Path) -> bool:
    """Copy only the Copilot CLI config file holding the OAuth token.

    ``config.json`` carries ``copilotTokens`` (the GitHub OAuth token) plus the
    last-logged-in user; it is all the CLI needs to authenticate. Sessions,
    logs and the session-store DB are deliberately left behind.
    """
    return _copy_named_credential_file(src, dst, "config.json")


def _copy_pi_credentials(src: Path, dst: Path) -> bool:
    """Copy only Pi's provider auth file"""
    auth_src = src / "agent" / "auth.json"
    if auth_src.is_symlink() or not auth_src.is_file() or not os.access(auth_src, os.R_OK):
        return False
    auth_dst = dst / "agent"
    auth_dst.mkdir(parents=True, exist_ok=True)
    shutil.copy2(auth_src, auth_dst / "auth.json")
    return True


def _copy_codex_credentials(src: Path, dst: Path) -> bool:
    """Copy only Codex auth material needed for a run, never sessions/logs."""
    copied = _copy_named_credential_file(src, dst, "auth.json")

    config_src = src / "config.toml"
    if not config_src.is_symlink() and config_src.is_file() and os.access(config_src, os.R_OK):
        copied = _copy_codex_bedrock_config(config_src, dst / "config.toml") or copied

    return copied


def _copy_codex_bedrock_config(src: Path, dst: Path) -> bool:
    """Write a minimal Codex Bedrock config without copying unrelated config."""
    try:
        with open(src, "rb") as f:
            config = tomllib.load(f)
    except (OSError, tomllib.TOMLDecodeError):
        return False

    if config.get("model_provider") != "amazon-bedrock":
        return False

    lines = ['model_provider = "amazon-bedrock"', ""]
    provider = config.get("model_providers", {}).get("amazon-bedrock", {})
    aws = provider.get("aws", {}) if isinstance(provider, dict) else {}
    region = aws.get("region") if isinstance(aws, dict) else None
    profile = aws.get("profile") if isinstance(aws, dict) else None
    if (isinstance(region, str) and region) or (isinstance(profile, str) and profile):
        lines.append("[model_providers.amazon-bedrock.aws]")
    if isinstance(region, str) and region:
        escaped_region = region.replace("\\", "\\\\").replace('"', '\\"')
        lines.append(f'region = "{escaped_region}"')
    if isinstance(profile, str) and profile:
        escaped_profile = profile.replace("\\", "\\\\").replace('"', '\\"')
        lines.append(f'profile = "{escaped_profile}"')
    if len(lines) > 2:
        lines.append("")

    dst.write_text("\n".join(lines))
    return True


class ContainerRunner:
    """Programmatic interface to Docker for running agent backends in isolation."""

    _CREDENTIAL_MOUNTS = {
        "aws": CredentialMount("/root/.aws", _copy_all_credentials),
        "claude": CredentialMount("/root/.claude", _copy_claude_credentials),
        "codex": CredentialMount("/root/.codex", _copy_codex_credentials),
        "copilot": CredentialMount("/root/.copilot", _copy_copilot_credentials),
        "pi": CredentialMount("/root/.pi", _copy_pi_credentials),
    }

    def build_docker_args(self, config: ContainerConfig) -> tuple[list[str], str]:
        """Build the `docker run` argument list from config."""
        cid_file = f"/tmp/tlaps-bench-{uuid.uuid4().hex[:8]}.cid"

        args = [
            "docker",
            "run",
            "--platform",
            "linux/amd64",
            "--rm",
            "--init",
            "-i",
            f"--cidfile={cid_file}",
        ]

        if config.cpus:
            args.append(f"--cpus={config.cpus}")
        if config.memory:
            args.append(f"--memory={config.memory}")

        if config.cap_net_admin and config.firewall_hosts:
            args.append("--cap-add=NET_ADMIN")

        # Workspace and result mounts
        if config.workspace:
            args.extend(["-v", f"{config.workspace}:/workspace:rw"])
        if config.result_dir:
            args.extend(["-v", f"{config.result_dir}:/results:rw"])
        if config.benchmark_dir:
            args.extend(["-v", f"{config.benchmark_dir}:/benchmark:ro"])

        # tlapm is baked into the image at /opt/tlapm

        # Credential directory mounts. Copy to throwaway tempdirs so agent
        # cannot modify host credentials. Cleaned up after run.
        self._credential_tmps: list[str] = []

        for name in config.credential_mounts:
            mount = self._CREDENTIAL_MOUNTS.get(name)
            if mount is None:
                raise ValueError(f"unknown credential mount: {name}")
            src = Path.home() / f".{name}"
            if src.is_dir():
                tmp = self._copy_credential_dir(name, src, mount)
                if tmp:
                    args.extend(["-v", f"{tmp}:{mount.mount_path}:rw"])

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
        """Build shell command: skills setup → install script → firewall → agent."""
        agent_cmd = " ".join(shlex.quote(c) for c in cmd)
        parts = [self._skills_setup_command()]
        if install_script:
            parts.append(f"/opt/install-scripts/{install_script} >&2")
        parts.append("/opt/firewall.sh >&2")
        parts.append(f"exec capsh --drop=cap_net_admin -- -c {shlex.quote(agent_cmd)}")
        return " && ".join(parts)

    @staticmethod
    def _skills_setup_command() -> str:
        """Link each agent's personal skills dir to the bundled skills.

        Runs after any credential mount is in place, so the link lands inside the
        mounted (throwaway) copy when present, and in the image layer otherwise —
        keeping bundled skills discoverable in both cases without touching host
        files. Skipped silently if the skills dir was not baked into the image.
        """
        links = " && ".join(
            f"ln -sfn {shlex.quote(_AGENT_SKILLS_DIR)} {shlex.quote(home + '/skills')}" for home in _AGENT_SKILL_HOMES
        )
        mkdirs = " ".join(shlex.quote(home) for home in _AGENT_SKILL_HOMES)
        return f"{{ [ -d {shlex.quote(_AGENT_SKILLS_DIR)} ] && mkdir -p {mkdirs} && {links} || true; }} >&2"

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

    def run_preflight(self, config: ContainerConfig, cmd: list[str], stdin_data: str, timeout: int = 180) -> None:
        """Validate a backend end-to-end before a full run. Raises on failure.

        Runs the real agent command (`cmd`) on a trivial prompt through the SAME
        install + firewall path as a real run (build_composite_command applies
        /opt/firewall.sh, then drops NET_ADMIN). This is what makes the check
        meaningful: it exercises the actual network sandbox, so a broken model
        id, an unknown CLI flag, missing credentials, or a firewall that blocks
        the auth host all surface here — instead of silently producing a whole
        sweep of 0-token FAILs. (The earlier preflight bypassed firewall.sh and
        so could not have caught an auth-host block.)
        """
        docker_args, cid_file = self.build_docker_args(config)
        composite = self.build_composite_command(cmd, config.install_script)
        full_cmd = docker_args + ["bash", "-c", composite]
        try:
            result = subprocess.run(full_cmd, input=stdin_data, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired as e:
            cid = self._read_cidfile(cid_file)
            if cid:
                self.kill_by_id(cid)
            raise RuntimeError(f"preflight timed out after {timeout}s") from e
        finally:
            self.cleanup_credential_tmps()
        if result.returncode != 0:
            output = (result.stderr or result.stdout or "").strip()
            if len(output) > 2000:
                output = "... (truncated) ...\n" + output[-2000:]
            raise RuntimeError(f"preflight failed (exit {result.returncode}):\n{output}")

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

    def cleanup_credential_tmps(self) -> None:
        """Remove throwaway credential directories."""
        for tmp in getattr(self, "_credential_tmps", []):
            shutil.rmtree(tmp, ignore_errors=True)
        self._credential_tmps = []

    def _copy_credential_dir(self, name: str, src: Path, mount: CredentialMount) -> str | None:
        """Copy host credentials into a throwaway directory and return its path."""
        tmp = tempfile.mkdtemp(prefix=f"tlaps-bench-{name}-")
        try:
            copied = mount.copy(src, Path(tmp))
            if not copied:
                shutil.rmtree(tmp, ignore_errors=True)
                return None
        except Exception:
            shutil.rmtree(tmp, ignore_errors=True)
            raise

        self._credential_tmps.append(tmp)
        return tmp

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
            ["docker", "build", "--platform", "linux/amd64", "-f", dockerfile, "-t", tag, context],
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


def ensure_image(force: bool = False) -> None:
    """Build the Docker image if missing or forced."""
    if force or not ContainerRunner.image_exists(IMAGE_TAG):
        dockerfile = os.path.join(_REPO_ROOT, "docker", "base.Dockerfile")
        if force:
            print("Building Docker image (--force-build)...")
        else:
            print("Docker image not found, building...")
        ContainerRunner.build_image(dockerfile, IMAGE_TAG, _REPO_ROOT)
