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


def test_base_image_keeps_the_local_build_fingerprint_label():
    dockerfile = (REPO_ROOT / "docker/base.Dockerfile").read_text()

    assert "ARG TLAPS_BENCH_BUILD_SHA256=unknown" in dockerfile
    assert 'LABEL org.specula.tlaps-bench.build-sha256="${TLAPS_BENCH_BUILD_SHA256}"' in dockerfile


def test_native_setup_follows_the_rolling_tlapm_release():
    """The tag is rolling, so the installer must not hard-code a specific build."""
    installer = (REPO_ROOT / "scripts/install_deps.sh").read_text()

    assert _match(r'^TLAPM_TAG="([^"]+)"', installer, "TLAPM_TAG in the installer")


def test_native_setup_rejects_a_tlapm_the_grader_cannot_use():
    """Guard the capability the rolling tag cannot guarantee.

    The grader shells out to ``tlapm --strict`` (tlaplus/tlapm#278) — a build
    without it rejects the flag and grades every task FAIL. Since the release
    asset is rebuilt in place, presence of a tlapm proves nothing: the installer
    has to probe the flag on both the existing and the freshly downloaded binary.
    """
    installer = (REPO_ROOT / "scripts/install_deps.sh").read_text()
    grader = (REPO_ROOT / "src/common/check_proof.py").read_text()

    assert '"--strict"' in grader, "grader no longer runs `tlapm --strict` — revisit this guard"
    assert 'tlapm_supports_strict "${HOME}/.tlapm/bin/tlapm"' in installer, "existing ~/.tlapm is not probed"
    assert 'tlapm_supports_strict "${STAGED_TLAPM}/bin/tlapm"' in installer, "downloaded tlapm is not probed"
