"""Run SANY over a .tla file and return its semantic model.

Thin wrapper around ``DumpSemantics`` (the tla2sany-based dumper). Reuses the
existing ``run.sh`` plumbing, which compiles the Java if needed and sets up the
TLA-Library search path (TLAPS stdlib + the input file's own directory so that
sibling-module EXTENDS/INSTANCE resolve).

This is the single entry point both the benchmark generator and the checker use
to get a parsed view of a module — no regex parsing of TLA+ source anywhere.
"""

from __future__ import annotations

import glob
import json
import os
import re
import shutil
import subprocess
import tempfile

from ..model import Module

_HERE = os.path.dirname(os.path.abspath(__file__))
# run.sh lives under the sany-dump location; we shell out to it rather than
# duplicating the build/launch logic. The path is overridable via SANY_RUN_SH so
# a frozen (PyInstaller) build — where __file__ points into the bundle, not the
# repo — can point at the run.sh baked into the image.
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, "..", "..", ".."))
_RUN_SH = os.environ.get(
    "SANY_RUN_SH",
    os.path.join(_REPO_ROOT, "src", "dataset", "sany-dump", "run.sh"),
)

_MARKER = "--- BEGIN SANY-DUMP JSON ---"


class SanyError(RuntimeError):
    """SANY failed to parse the module (parse/semantic error, or no output)."""


def dump_raw(tla_path: str, timeout: int = 180) -> dict:
    """Run SANY on ``tla_path`` and return the raw JSON dict."""
    res = subprocess.run(
        [_RUN_SH, tla_path],
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    out = res.stdout
    idx = out.find(_MARKER)
    if idx < 0:
        err = (res.stderr or "").strip()
        raise SanyError(f"SANY produced no dump for {tla_path} (exit {res.returncode}). stderr: {err[:400]}")
    try:
        return json.loads(out[idx + len(_MARKER) :])
    except json.JSONDecodeError as e:
        raise SanyError(f"Could not parse SANY dump for {tla_path}: {e}") from e


def dump(tla_path: str, timeout: int = 180) -> Module:
    """Run SANY on ``tla_path`` and return a typed :class:`Module`."""
    return Module.parse(dump_raw(tla_path, timeout=timeout))


def try_dump(tla_path: str, timeout: int = 180) -> Module | None:
    """Like :func:`dump` but returns ``None`` on any SANY failure.

    Useful when scanning a set of files where some may legitimately fail to
    parse in isolation (e.g. a dependency missing its own deps).
    """
    try:
        return dump(tla_path, timeout=timeout)
    except (SanyError, subprocess.TimeoutExpired, OSError):
        return None


_MODULE_DECL = re.compile(r"^-+\s*MODULE\s+(\w+)", re.MULTILINE)


def module_name_of(tla_path: str) -> str | None:
    """Read the declared module name from a .tla file's header."""
    try:
        with open(tla_path, encoding="utf-8", errors="ignore") as f:
            m = _MODULE_DECL.search(f.read())
        return m.group(1) if m else None
    except OSError:
        return None


def _as_dep_dirs(dep_dir, dep_dirs) -> list:
    if dep_dirs:
        return list(dep_dirs)
    if dep_dir:
        return [dep_dir]
    return []


def dump_normalized(
    tla_path: str, dep_dir: str | None = None, timeout: int = 180, dep_dirs: list | None = None
) -> Module:
    """Parse ``tla_path`` robustly: correct filename + supply dependency modules.

    Two real-world hurdles this clears:
      * TLA+/SANY requires the file name to match the declared module name, but
        submissions are often stored as ``solution.tla``.
      * An archived result dir frequently keeps only ``benchmark.tla`` +
        ``solution.tla`` and drops the dependency modules (Voting.tla,
        PConProof.tla, ...). SANY then fails with "Cannot find source for
        module X" — which looks like a parse failure but is just a missing dep.

    We copy every ``*.tla`` from each ``dep_dirs`` entry (later entries win on
    name clashes, so the submission's own copy overrides a canonical one) into a
    temp dir, rename the target to ``<module>.tla``, and parse there. Pass both
    the canonical ``benchmark/<level>/<module>/`` dir (for the given deps) and
    the result dir (for the submission + any agent-created modules).
    """
    mod = module_name_of(tla_path)
    dirs = _as_dep_dirs(dep_dir, dep_dirs) or [os.path.dirname(os.path.abspath(tla_path))]
    base = os.path.basename(tla_path)
    # Fast path: filename matches AND a single dep dir == the file's own dir.
    if (
        mod
        and base == f"{mod}.tla"
        and len(dirs) == 1
        and os.path.abspath(dirs[0]) == os.path.dirname(os.path.abspath(tla_path))
    ):
        return dump(tla_path, timeout=timeout)

    tmp = tempfile.mkdtemp(prefix="tlacore_sany_")
    try:
        for d in dirs:
            for dep in glob.glob(os.path.join(d, "*.tla")):
                shutil.copy2(dep, os.path.join(tmp, os.path.basename(dep)))
        target = os.path.join(tmp, f"{mod}.tla") if mod else os.path.join(tmp, base)
        shutil.copy2(tla_path, target)
        return dump(target, timeout=timeout)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def try_dump_normalized(
    tla_path: str, dep_dir: str | None = None, timeout: int = 180, dep_dirs: list | None = None
) -> Module | None:
    try:
        return dump_normalized(tla_path, dep_dir=dep_dir, timeout=timeout, dep_dirs=dep_dirs)
    except (SanyError, subprocess.TimeoutExpired, OSError):
        return None
