"""Official proof-library source provenance and frozen catalog tests."""

from __future__ import annotations

import json

import pytest

from common.proof_libraries import (
    OfficialLibraryCatalog,
    ProofLibraryError,
    scan_official_libraries,
    tree_digest,
    validate_official_imports,
)


def _source(root, source_name: str, repository: str, commit: str, module: str):
    directory = root / source_name
    directory.mkdir()
    (directory / f"{module}.tla").write_text(f"---- MODULE {module} ----\n====\n")
    (directory / f"{module}_proofs.tla").write_text(f"---- MODULE {module}_proofs ----\n====\n")
    digest = tree_digest(directory)
    marker = {
        "schema_version": 1,
        "source": source_name,
        "repository": repository,
        "commit": commit,
        "tree_sha256": digest,
    }
    (directory / ".proof-library-source.json").write_text(json.dumps(marker))
    return directory, digest


def _fixture(tmp_path):
    tlapm_commit = "1" * 40
    community_commit = "2" * 40
    tlapm, tlapm_digest = _source(tmp_path, "tlapm", "tlaplus/tlapm", tlapm_commit, "TLAPS")
    community, community_digest = _source(
        tmp_path,
        "community_modules",
        "tlaplus/CommunityModules",
        community_commit,
        "Graphs",
    )
    lock = {
        "schema_version": 1,
        "sources": {
            "tlapm": {
                "repository": "tlaplus/tlapm",
                "commit": tlapm_commit,
                "tracking_ref": "main",
                "subdirectory": "library",
                "destination": "tlapm",
                "tree_sha256": tlapm_digest,
            },
            "community_modules": {
                "repository": "tlaplus/CommunityModules",
                "commit": community_commit,
                "tracking_ref": "master",
                "subdirectory": "modules",
                "destination": "community",
                "tree_sha256": community_digest,
            },
        },
    }
    lock_path = tmp_path / "sources.json"
    lock_path.write_text(json.dumps(lock))
    return lock_path, tlapm, community


def test_scan_freezes_public_modules_from_the_two_official_sources(tmp_path):
    lock, tlapm, community = _fixture(tmp_path)

    catalog = scan_official_libraries(
        source_lock=lock,
        tlapm_library=tlapm,
        community_library=community,
    )

    assert catalog.allowed_modules == {"TLAPS", "Graphs"}
    assert OfficialLibraryCatalog.from_bytes(catalog.to_bytes()).digest == catalog.digest


def test_scan_rejects_library_content_drift(tmp_path):
    lock, tlapm, community = _fixture(tmp_path)
    (tlapm / "TLAPS.tla").write_text("---- MODULE TLAPS ----\nChanged == TRUE\n====\n")

    with pytest.raises(ProofLibraryError, match="content drifted"):
        scan_official_libraries(
            source_lock=lock,
            tlapm_library=tlapm,
            community_library=community,
        )


def test_catalog_rejects_tampered_digest(tmp_path):
    lock, tlapm, community = _fixture(tmp_path)
    catalog = scan_official_libraries(
        source_lock=lock,
        tlapm_library=tlapm,
        community_library=community,
    )
    value = json.loads(catalog.to_bytes())
    value["modules"]["Injected"] = value["modules"]["TLAPS"]

    with pytest.raises(ProofLibraryError, match="digest"):
        OfficialLibraryCatalog.from_bytes(json.dumps(value).encode())


def _task(helper: str) -> str:
    return (
        "---- MODULE Task ----\n"
        "EXTENDS Model\n"
        "\\* BEGIN AGENT HELPERS\n"
        f"{helper}\n"
        "\\* END AGENT HELPERS\n"
        "THEOREM TRUE\n"
        "\\* BEGIN AGENT PROOF\n"
        "PROOF OBVIOUS\n"
        "\\* END AGENT PROOF\n"
        "====\n"
    )


def test_import_validator_accepts_named_official_module():
    source = _task("LOCAL FST == INSTANCE FiniteSetTheorems")

    assert validate_official_imports(source, frozenset({"FiniteSetTheorems"})) == []


@pytest.mark.parametrize(
    ("helper", "code"),
    [
        ("LOCAL Bad == INSTANCE WorkspaceProofs", "IMPORT_NOT_ALLOWED"),
        ("LOCAL INSTANCE TLAPS", "IMPORT_ALIAS_REQUIRED"),
        ("LOCAL FST == INSTANCE FiniteSetTheorems WITH S <- Nodes", "IMPORT_WITH_FORBIDDEN"),
        ("FST == INSTANCE FiniteSetTheorems", "IMPORT_SYNTAX"),
    ],
)
def test_import_validator_returns_simple_policy_errors(helper, code):
    violations = validate_official_imports(_task(helper), frozenset({"TLAPS", "FiniteSetTheorems"}))

    assert [violation.code for violation in violations] == [code]


def test_import_validator_ignores_comments_and_strings():
    source = _task('Text == "INSTANCE Fake"\n\\* INSTANCE Fake')

    assert validate_official_imports(source, frozenset()) == []


def test_import_validator_rejects_instance_outside_helper_region():
    source = _task("").replace("PROOF OBVIOUS", "PROOF\n<1>1. LOCAL INSTANCE TLAPS\n<1>2. QED OBVIOUS")

    violations = validate_official_imports(source, frozenset({"TLAPS"}))

    assert [violation.code for violation in violations] == ["IMPORT_OUTSIDE_HELPERS"]
