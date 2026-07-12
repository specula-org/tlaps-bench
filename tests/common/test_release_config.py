"""Release configuration guard for Docker publishing."""

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def _match(pattern: str, text: str, description: str) -> str:
    match = re.search(pattern, text, re.MULTILINE)
    assert match, f"missing {description}"
    return match.group(1)


def test_docker_publish_workflow_references_an_existing_dockerfile():
    workflow = (REPO_ROOT / ".github/workflows/docker-image.yml").read_text()
    dockerfile = _match(r"^\s*file:\s*(\S+)\s*$", workflow, "Dockerfile path in publish workflow")

    assert (REPO_ROOT / dockerfile).is_file(), f"publish workflow references missing file: {dockerfile}"
