#!/usr/bin/env python3
"""Install and inspect the pinned official TLA+ proof-library sources."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import shutil
import sys
import tarfile
import tempfile
import urllib.error
import urllib.request
from pathlib import Path, PurePosixPath

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LOCK = REPO_ROOT / "config" / "proof-library-sources.json"
MARKER_FILENAME = ".proof-library-source.json"


def _canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def _load_lock(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read proof-library source lock {path}: {exc}") from exc
    if type(value) is not dict or value.get("schema_version") != 1 or type(value.get("sources")) is not dict:
        raise ValueError(f"invalid proof-library source lock: {path}")
    for name, source in value["sources"].items():
        required = {"repository", "commit", "tracking_ref", "subdirectory", "destination", "tree_sha256"}
        if type(name) is not str or type(source) is not dict or set(source) != required:
            raise ValueError(f"invalid proof-library source entry {name!r}")
        if not all(type(source[key]) is str and source[key] for key in required):
            raise ValueError(f"proof-library source entry {name!r} contains an empty or non-string field")
        commit = source["commit"]
        if len(commit) != 40 or any(char not in "0123456789abcdef" for char in commit):
            raise ValueError(f"proof-library source entry {name!r} has an invalid commit")
        destination = PurePosixPath(source["destination"])
        if destination.is_absolute() or len(destination.parts) != 1 or destination.name in {"", ".", ".."}:
            raise ValueError(f"proof-library source entry {name!r} has an invalid destination")
    return value


def _update_digest(digest: hashlib._Hash, value: bytes) -> None:
    digest.update(len(value).to_bytes(8, byteorder="big"))
    digest.update(value)


def tree_digest(directory: Path) -> str:
    """Hash the sorted top-level .tla filenames and bytes in one library."""

    digest = hashlib.sha256()
    files = sorted(directory.glob("*.tla"), key=lambda path: path.name)
    if not files:
        raise ValueError(f"official proof-library directory contains no .tla modules: {directory}")
    for path in files:
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"official proof-library module must be a regular file: {path}")
        _update_digest(digest, path.name.encode())
        _update_digest(digest, path.read_bytes())
    return digest.hexdigest()


def _download_archive(repository: str, commit: str) -> bytes:
    url = f"https://github.com/{repository}/archive/{commit}.tar.gz"
    request = urllib.request.Request(url, headers={"User-Agent": "tlaps-bench-proof-library-installer"})
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            return response.read()
    except (OSError, urllib.error.URLError) as exc:
        raise ValueError(f"failed to download official proof libraries from {url}: {exc}") from exc


def _extract_modules(archive: bytes, source: dict, destination: Path) -> None:
    expected_suffix = PurePosixPath(source["subdirectory"])
    found = 0
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as bundle:
        for member in bundle.getmembers():
            path = PurePosixPath(member.name)
            if not member.isfile() or path.suffix != ".tla" or len(path.parts) < 3:
                continue
            relative = PurePosixPath(*path.parts[1:])
            if relative.parent != expected_suffix:
                continue
            extracted = bundle.extractfile(member)
            if extracted is None:
                raise ValueError(f"cannot extract official proof-library module {member.name}")
            (destination / relative.name).write_bytes(extracted.read())
            found += 1
    if found == 0:
        raise ValueError(
            f"official source {source['repository']}@{source['commit']} contains no top-level "
            f".tla modules under {source['subdirectory']}"
        )


def _marker(source_name: str, source: dict, digest: str) -> dict:
    return {
        "schema_version": 1,
        "source": source_name,
        "repository": source["repository"],
        "commit": source["commit"],
        "tree_sha256": digest,
    }


def _installed_matches(destination: Path, expected_marker: dict) -> bool:
    marker_path = destination / MARKER_FILENAME
    try:
        marker = json.loads(marker_path.read_text(encoding="utf-8"))
        return marker == expected_marker and tree_digest(destination) == expected_marker["tree_sha256"]
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError):
        return False


def _stage_source(source_name: str, source: dict, parent: Path) -> tuple[Path, str]:
    archive = _download_archive(source["repository"], source["commit"])
    destination = parent / source["destination"]
    destination.mkdir()
    _extract_modules(archive, source, destination)
    digest = tree_digest(destination)
    expected = source["tree_sha256"]
    if expected != "pending" and digest != expected:
        raise ValueError(
            f"official proof-library tree hash mismatch for {source_name}: expected {expected}, got {digest}"
        )
    return destination, digest


def install(lock: dict, root: Path) -> None:
    root.mkdir(parents=True, exist_ok=True)
    for source_name, source in lock["sources"].items():
        destination = root / source["destination"]
        expected_marker = _marker(source_name, source, source["tree_sha256"])
        if source["tree_sha256"] != "pending" and _installed_matches(destination, expected_marker):
            print(f"[proof-libraries] {source_name} {source['commit'][:12]} already installed")
            continue
        with tempfile.TemporaryDirectory(prefix=f"proof-libraries-{source_name}-") as temporary:
            staged, digest = _stage_source(source_name, source, Path(temporary))
            marker = _marker(source_name, source, digest)
            (staged / MARKER_FILENAME).write_bytes(_canonical_json(marker))
            if destination.exists():
                shutil.rmtree(destination)
            shutil.copytree(staged, destination)
        print(f"[proof-libraries] installed {source_name} {source['commit'][:12]} ({digest[:12]})")


def inspect(lock: dict) -> None:
    with tempfile.TemporaryDirectory(prefix="proof-libraries-inspect-") as temporary:
        parent = Path(temporary)
        for source_name, source in lock["sources"].items():
            destination, digest = _stage_source(source_name, source, parent)
            count = len(list(destination.glob("*.tla")))
            print(f"{source_name}: {count} modules, tree_sha256={digest}")


def check_upstream(lock: dict) -> None:
    for source_name, source in lock["sources"].items():
        url = f"https://api.github.com/repos/{source['repository']}/commits/{source['tracking_ref']}"
        request = urllib.request.Request(
            url, headers={"Accept": "application/vnd.github+json", "User-Agent": "tlaps-bench"}
        )
        try:
            with urllib.request.urlopen(request, timeout=10) as response:
                latest = json.load(response)["sha"]
        except (OSError, KeyError, ValueError, urllib.error.URLError) as exc:
            print(f"WARNING: could not check {source_name} for upstream updates: {exc}", file=sys.stderr)
            continue
        if latest != source["commit"]:
            print(
                f"WARNING: {source_name} has a newer upstream commit {latest[:12]}; "
                f"the audited source lock remains {source['commit'][:12]}.",
                file=sys.stderr,
            )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("install", "inspect", "check-upstream"))
    parser.add_argument("--lock", type=Path, default=DEFAULT_LOCK)
    parser.add_argument("--root", type=Path, default=REPO_ROOT / "lib")
    args = parser.parse_args()
    try:
        lock = _load_lock(args.lock)
        if args.command == "install":
            install(lock, args.root)
        elif args.command == "inspect":
            inspect(lock)
        else:
            check_upstream(lock)
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
