"""Release configuration guard for Docker publishing."""

import json
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


def test_official_proof_library_sources_are_pinned_for_native_and_docker_setups():
    installer = (REPO_ROOT / "scripts/install_deps.sh").read_text()
    dockerfile = (REPO_ROOT / "docker/base.Dockerfile").read_text()
    lock = json.loads((REPO_ROOT / "config/proof-library-sources.json").read_text())

    assert lock["schema_version"] == 1
    assert set(lock["sources"]) == {"tlapm", "community_modules"}
    for source in lock["sources"].values():
        assert re.fullmatch(r"[0-9a-f]{40}", source["commit"])
        assert re.fullmatch(r"[0-9a-f]{64}", source["tree_sha256"])
    assert "scripts/install_proof_libraries.py" in installer
    assert "config/proof-library-sources.json" in dockerfile
    assert "scripts/install_proof_libraries.py" in dockerfile
    assert "TLAPS_LIB=/opt/proof-libraries/tlapm" in dockerfile
    assert "COMMUNITY_LIB=/opt/proof-libraries/community" in dockerfile


def test_verification_toolchain_artifacts_are_content_locked_for_native_and_docker_setups():
    installer = (REPO_ROOT / "scripts/install_deps.sh").read_text()
    dockerfile = (REPO_ROOT / "docker/base.Dockerfile").read_text()
    workflow = (REPO_ROOT / ".github/workflows/ci.yml").read_text()
    lock = json.loads((REPO_ROOT / "config/verification-toolchain.json").read_text())

    assert lock["schema_version"] == 1
    assert set(lock["tools"]) == {"tlapm", "sany"}
    artifacts = [*lock["tools"]["tlapm"]["platforms"].values(), lock["tools"]["sany"]]
    assert all(re.fullmatch(r"[0-9a-f]{64}", artifact["sha256"]) for artifact in artifacts)
    assert "config/verification-toolchain.json" in installer
    assert "verify-artifact tlapm" in installer
    assert "verify-artifact sany" in installer
    assert "config/verification-toolchain.json" in dockerfile
    assert "verify-artifact tlapm" in dockerfile
    assert "verify-artifact sany" in dockerfile
    assert "config/verification-toolchain.json" in workflow


def test_native_setup_rejects_a_tlapm_the_grader_cannot_use():
    """Guard the capability required in addition to the content lock.

    The grader shells out to ``tlapm --strict`` (tlaplus/tlapm#278) — a build
    without it rejects the flag and grades every task FAIL. The installer probes
    the flag on both the existing and freshly downloaded locked binary.
    """
    installer = (REPO_ROOT / "scripts/install_deps.sh").read_text()
    grader = (REPO_ROOT / "src/common/check_proof.py").read_text()

    assert '"--strict"' in grader, "grader no longer runs `tlapm --strict` — revisit this guard"
    assert 'tlapm_supports_strict "${HOME}/.tlapm/bin/tlapm"' in installer, "existing ~/.tlapm is not probed"
    assert 'tlapm_supports_strict "${STAGED_TLAPM}/bin/tlapm"' in installer, "downloaded tlapm is not probed"
