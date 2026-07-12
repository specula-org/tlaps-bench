"""Release configuration guards for Docker publishing and toolchain pinning."""

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


def test_docker_and_native_setup_pin_the_same_tlapm_build():
    dockerfile = (REPO_ROOT / "docker/base.Dockerfile").read_text()
    native_setup = (REPO_ROOT / "scripts/install_deps.sh").read_text()

    docker_tag = _match(r"^ARG TLAPM_TAG=(\S+)$", dockerfile, "Docker TLAPM tag")
    docker_commit = _match(r"^ARG TLAPM_COMMIT=(\S+)$", dockerfile, "Docker TLAPM commit")
    native_tag = _match(r'^TLAPM_TAG="([^"]+)"$', native_setup, "native TLAPM tag")
    native_commit = _match(r'^TLAPM_COMMIT="([^"]+)"$', native_setup, "native TLAPM commit")

    assert (docker_tag, docker_commit) == (native_tag, native_commit)
    assert '/opt/tlapm/bin/tlapm --version | grep -F "${TLAPM_COMMIT}"' in dockerfile
