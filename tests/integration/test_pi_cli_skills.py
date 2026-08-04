"""Exercise Pi's installed project-skill discovery without a model request."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

REQUIRE_PI_CLI = os.environ.get("TLAPS_BENCH_REQUIRE_PI_CLI") == "1"


def _installed_pi() -> str | None:
    binary = shutil.which("pi")
    if binary is None:
        return None
    try:
        result = subprocess.run(
            [binary, "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    help_text = f"{result.stdout}\n{result.stderr}"
    required_flags = ("--mode", "--offline", "--approve", "--no-approve", "--skill")
    return binary if result.returncode == 0 and all(flag in help_text for flag in required_flags) else None


PI_BINARY = _installed_pi()


def _write_skill(workspace: Path, name: str) -> None:
    skill_dir = workspace / ".agents" / "skills" / name
    skill_dir.mkdir(parents=True)
    (skill_dir / "SKILL.md").write_text(
        f"---\nname: {name}\ndescription: Use when testing {name} discovery.\n---\n\n# {name}\n"
    )


def _write_project_extension(workspace: Path) -> None:
    extension_dir = workspace / ".pi" / "extensions"
    extension_dir.mkdir(parents=True)
    (extension_dir / "project-extension.ts").write_text(
        "export default function (pi: any) {\n"
        '  pi.registerCommand("project-extension", {\n'
        '    description: "Project extension loaded",\n'
        "    handler: async () => {},\n"
        "  });\n"
        "}\n"
    )


def _project_commands(binary: str, workspace: Path, profile: str, *resource_options: str) -> dict[str, str]:
    home = workspace.parent / f"{profile}-home"
    agent_dir = workspace.parent / f"{profile}-pi-agent"
    home.mkdir()
    agent_dir.mkdir()
    env = {
        **os.environ,
        "HOME": str(home),
        "PI_CODING_AGENT_DIR": str(agent_dir),
    }
    result = subprocess.run(
        [
            binary,
            "--mode",
            "rpc",
            "--offline",
            "--no-session",
            "--no-context-files",
            *resource_options,
        ],
        input='{"type":"get_commands"}\n',
        capture_output=True,
        text=True,
        timeout=20,
        cwd=workspace,
        env=env,
    )
    assert result.returncode == 0, result.stderr or result.stdout
    responses = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    response = next(event for event in responses if event.get("command") == "get_commands")
    return {command["name"]: command["source"] for command in response["data"]["commands"]}


@pytest.mark.skipif(
    PI_BINARY is None and not REQUIRE_PI_CLI,
    reason="installed Pi CLI lacks the current offline RPC interface",
)
def test_real_pi_cli_loads_explicit_skills_without_trusting_project_extensions(tmp_path):
    binary = PI_BINARY
    assert binary is not None, "Pi CLI is required"
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    _write_skill(workspace, "zeta-skill")
    _write_skill(workspace, "alpha-skill")
    _write_project_extension(workspace)

    approved = _project_commands(binary, workspace, "approved", "--approve")
    assert approved["skill:alpha-skill"] == "skill"
    assert approved["skill:zeta-skill"] == "skill"
    assert approved["project-extension"] == "extension"

    restricted = _project_commands(
        binary,
        workspace,
        "restricted",
        "--no-approve",
        "--skill",
        ".agents/skills",
    )
    assert restricted["skill:alpha-skill"] == "skill"
    assert restricted["skill:zeta-skill"] == "skill"
    assert "project-extension" not in restricted
