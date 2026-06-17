"""Import proven TLA+ specs from a tlaplus/Examples checkout into source/.

For each selected spec <S>:
  - read Examples/specifications/<S>/manifest.json
  - the modules with a "proof" key are the proof targets
  - resolve each proof module's EXTENDS/INSTANCE deps transitively, classifying
    each referenced module as:
        resolvable -> skip (tlapm finds it via an -I path: bundled stdlib or
                      vendored CommunityModules in lib/community/)
        local      -> copy + recurse
        (a proof module is skipped only if a local dep is missing, or its
         filename != its MODULE name)
  - copy the importable proof modules + their local deps into
    source/tlaplus_examples_<S>/  (per-subdir bucket for specs whose proof
    modules live in subdirectories, e.g. SpecifyingSystems)

Only files reachable from a proof module via EXTENDS/INSTANCE are copied, so
model/animation/trace files (MC*, *.cfg, *.pdf, etc.) are never candidates.

This does NOT run tlapm or the generator; it only stages files. Validation is a
separate step (run tlapm directly on each copied proof module).

Usage:
  python3 scripts/import_tlaps_example.py --examples ../Examples --spec DieHard
  python3 scripts/import_tlaps_example.py --examples ../Examples --spec CigaretteSmokers --spec ewd998
  python3 scripts/import_tlaps_example.py --examples ../Examples --all
"""

import argparse
import json
import os
import re
import shutil
import sys
from pathlib import Path

# Single source of truth for module classification lives in the L1 generator.
sys.path.insert(
    0,
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src", "dataset", "level1"),
)
from generate import RESOLVABLE_MODULES  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = REPO_ROOT / "source"


def parse_module_name(text: str):
    m = re.search(r"-+\s*MODULE\s+(\w+)\s*-+", text)
    return m.group(1) if m else None


def strip_comments(text: str) -> str:
    """Remove (* ... *) block comments (nested) and \\* line comments.
    Good enough for EXTENDS/INSTANCE scanning; not string-literal aware."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if two == "(*":
            depth += 1
            i += 2
            continue
        if two == "*)" and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        if two == "\\*":  # line comment to end of line
            j = text.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def parse_extends(text: str):
    """Extract EXTENDS modules, handling multi-line EXTENDS that wraps onto
    indented continuation lines:
        EXTENDS Foo, Bar,
                Baz, TLAPS
    """
    text = strip_comments(text)
    lines = text.split("\n")
    for i, line in enumerate(lines):
        m = re.match(r"^EXTENDS\s+(.+)$", line)
        if not m:
            continue
        parts, cur, j = [], m.group(1), i
        while True:
            parts.append(cur)
            if cur.rstrip().endswith(","):
                j += 1
                if j < len(lines):
                    cur = lines[j]
                    continue
            break
        joined = " ".join(parts)
        return [x.strip() for x in joined.split(",") if x.strip()]
    return []


def parse_instances(text: str):
    text = strip_comments(text)
    mods = []
    for m in re.finditer(r"(?:(\w+)\s*==\s*)?INSTANCE\s+(\w+)", text):
        mods.append(m.group(2))
    return mods


def classify(mod: str) -> str:
    if mod in RESOLVABLE_MODULES:
        return "resolvable"  # stdlib or vendored community — tlapm finds it, don't copy
    return "local"  # assume local until proven otherwise (file presence checked by caller)


def proof_modules_from_manifest(spec_dir: Path):
    """Return list of module paths (relative to spec_dir) that have a 'proof'
    key, or None if there's no manifest. Paths may include a subdirectory
    component (e.g. SpecifyingSystems/FIFO/InnerFIFO_proof.tla). Raises
    ValueError on a malformed manifest."""
    mf = spec_dir / "manifest.json"
    if not mf.is_file():
        return None  # signal: no manifest
    try:
        data = json.loads(mf.read_text())
    except (json.JSONDecodeError, OSError) as e:
        raise ValueError(f"bad manifest.json: {e}") from e
    out = []
    for mod in data.get("modules", []):
        if "proof" not in mod:
            continue
        # manifest path is "specifications/<spec>/<...>/<file>.tla"; keep the
        # part below the spec dir so we know any subdirectory.
        parts = mod["path"].split("/")
        if "specifications" in parts:
            idx = parts.index("specifications")
            rel = "/".join(parts[idx + 2 :])  # drop "specifications/<spec>/"
        else:
            rel = os.path.basename(mod["path"])
        out.append(rel)
    return out


def spec_units(spec, examples_root):
    """Expand a spec into import units. Normally one unit (the spec dir). If the
    spec's proof modules live in subdirectories (e.g. SpecifyingSystems), emit
    one unit per subdir so each is a self-contained, collision-free bucket:
      unit_name  -> tlaplus_examples_<spec>[_<subdir>]
      unit_dir   -> spec dir, or spec/<subdir>
      basenames  -> proof-module filenames within that dir

    Returns (units, error). units is a list of (unit_name, unit_dir, basenames).
    """
    spec_dir = examples_root / "specifications" / spec
    if not spec_dir.is_dir():
        return None, f"spec dir not found: {spec_dir}"
    try:
        rel_paths = proof_modules_from_manifest(spec_dir)
    except ValueError as e:
        return None, str(e)
    if rel_paths is None:
        return None, "no manifest.json"
    if not rel_paths:
        return None, "no proof-keyed modules in manifest"

    by_subdir = {}
    for rel in rel_paths:
        subdir = os.path.dirname(rel)  # "" if directly in spec dir
        by_subdir.setdefault(subdir, []).append(os.path.basename(rel))

    units = []
    for subdir in sorted(by_subdir):
        if subdir:
            unit_name = f"tlaplus_examples_{spec}_{subdir.replace('/', '_')}"
            unit_dir = spec_dir / subdir
        else:
            unit_name = f"tlaplus_examples_{spec}"
            unit_dir = spec_dir
        units.append((unit_name, unit_dir, by_subdir[subdir]))
    return units, None


def _resolve_one(start_name, local_by_name):
    """Resolve transitive local deps + missing modules for ONE proof module.

    Returns (to_copy:set[basename], missing:set). Modules tlapm resolves via an
    -I path (stdlib or vendored community) are skipped, not copied.
    """
    to_copy, missing = set(), set()
    fp0 = local_by_name.get(start_name)
    if fp0 is not None:
        to_copy.add(fp0.name)
    visited = {start_name}
    work = [start_name]
    while work:
        cur = work.pop()
        fp = local_by_name.get(cur)
        if not fp:
            continue
        text = fp.read_text()
        for d in parse_extends(text) + parse_instances(text):
            if classify(d) == "resolvable":
                continue
            if d in local_by_name:
                to_copy.add(local_by_name[d].name)
                if d not in visited:
                    visited.add(d)
                    work.append(d)
            else:
                missing.add(d)
    return to_copy, missing


def resolve_unit(unit_dir: Path, proof_basenames):
    """Resolve, PER PROOF MODULE, the local .tla files to copy + any missing
    deps within unit_dir. Modules tlapm resolves via an -I path (stdlib or
    vendored community) are skipped. A proof module is "ok" if all its
    non-resolvable deps are present locally; otherwise it's skipped
    (missing-file / missing-deps / module-name-mismatch).

    Returns dict with: per_module, to_copy (union over ok modules),
    skipped_modules, proof_modules.
    """
    local_by_name = {}
    for p in unit_dir.glob("*.tla"):
        name = parse_module_name(p.read_text())
        if name:
            local_by_name[name] = p

    result = {
        "proof_modules": list(proof_basenames),
        "per_module": {},
        "to_copy": set(),
        "skipped_modules": {},
    }

    for base in proof_basenames:
        p = unit_dir / base
        if not p.is_file():
            result["per_module"][base] = {
                "to_copy": set(),
                "missing": {base},
                "ok": False,
            }
            result["skipped_modules"][base] = f"missing-file: {base}"
            continue
        nm = parse_module_name(p.read_text())
        # No parseable MODULE header -> not a valid TLA+ module; skip rather
        # than fall through to _resolve_one(None) (which would report ok with
        # nothing copied, silently dropping the proof module).
        if nm is None:
            result["per_module"][base] = {
                "to_copy": set(),
                "missing": set(),
                "ok": False,
            }
            result["skipped_modules"][base] = f"no-module-header: {base}"
            continue
        # tlapm requires filename == module name; flag rather than silently
        # rename (e.g. TPaxosWithProof.tla declares MODULE TPaxos).
        if f"{nm}.tla" != base:
            result["per_module"][base] = {
                "to_copy": set(),
                "missing": set(),
                "ok": False,
            }
            result["skipped_modules"][base] = f"module-name-mismatch: file {base} declares MODULE {nm}"
            continue
        to_copy, missing = _resolve_one(nm, local_by_name)
        ok = not missing
        result["per_module"][base] = {"to_copy": to_copy, "missing": missing, "ok": ok}
        if ok:
            result["to_copy"] |= to_copy
        else:
            result["skipped_modules"][base] = "missing-deps: " + ",".join(sorted(missing))
    return result


def import_unit(unit_name, unit_dir, proof_basenames, dry_run=False, include_unvalidatable=False):
    """Import one unit (a spec, or a subdir of a spec) into
    source/<unit_name>/. Returns a report dict."""
    res = resolve_unit(unit_dir, proof_basenames)

    ok_modules = [b for b, info in res["per_module"].items() if info["ok"]]
    to_copy = set()
    if include_unvalidatable:
        for info in res["per_module"].values():  # stage everything (debug)
            to_copy |= info["to_copy"]
    else:
        for b in ok_modules:
            to_copy |= res["per_module"][b]["to_copy"]

    dest = SOURCE_ROOT / unit_name
    report = {
        "spec": unit_name,
        "dest": str(dest.relative_to(REPO_ROOT)),
        "proof_modules": res["proof_modules"],
        "ok_modules": ok_modules,
        "skipped_modules": res["skipped_modules"],
        "copied": sorted(to_copy),
        "skipped": (not ok_modules) and not include_unvalidatable,
        "error": None,
    }

    if dry_run:
        return report

    # Nothing importable -> don't leave a doomed dir.
    if not to_copy:
        if dest.exists():
            shutil.rmtree(dest)
        return report

    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    for base in sorted(to_copy):
        src = unit_dir / base
        if src.is_file():
            shutil.copy2(src, dest / base)
    return report


def import_spec(spec, examples_root, dry_run=False, include_unvalidatable=False):
    """Import a spec, expanding it into one or more units (per subdir when the
    spec's proof modules live in subdirectories). Returns a list of reports."""
    units, err = spec_units(spec, examples_root)
    if err:
        return [{"spec": spec, "error": err}]
    return [import_unit(name, d, bases, dry_run, include_unvalidatable) for (name, d, bases) in units]


def main():
    ap = argparse.ArgumentParser(description="Import proven Examples specs into source/")
    ap.add_argument("--examples", required=True, help="path to tlaplus/Examples checkout")
    ap.add_argument("--spec", action="append", default=[], help="spec name (repeatable)")
    ap.add_argument("--all", action="store_true", help="import every spec with a proof-keyed module")
    ap.add_argument("--dry-run", action="store_true", help="resolve + report, do not copy")
    ap.add_argument(
        "--include-unvalidatable",
        action="store_true",
        help="also stage proof modules with missing deps / module-name mismatch (default: skip them)",
    )
    args = ap.parse_args()

    examples_root = Path(args.examples).resolve()
    if not (examples_root / "specifications").is_dir():
        print(f"ERROR: {examples_root}/specifications not found", file=sys.stderr)
        sys.exit(1)

    specs = list(args.spec)
    if args.all:
        for mf in (examples_root / "specifications").glob("*/manifest.json"):
            try:
                pm = proof_modules_from_manifest(mf.parent)
            except ValueError:
                pm = None  # malformed manifest; surfaced as an error row in import_spec
            if pm:
                specs.append(mf.parent.name)
    specs = sorted(set(specs))
    if not specs:
        print("No specs selected. Use --spec NAME or --all.", file=sys.stderr)
        sys.exit(1)

    reports = []
    for s in specs:
        reports.extend(
            import_spec(
                s,
                examples_root,
                dry_run=args.dry_run,
                include_unvalidatable=args.include_unvalidatable,
            )
        )

    # Print a compact table
    print(f"{'spec':<32} {'proof':<6} {'copied':<7} {'status'}")
    print("-" * 80)
    n_ok = n_skip = n_err = 0
    partial = []  # specs where some proof modules were skipped
    for r in reports:
        if r.get("error"):
            n_err += 1
            print(f"{r['spec']:<32} {'-':<6} {'-':<7} ERROR: {r['error']}")
            continue
        nproof = len(r["proof_modules"])
        nskipmod = len(r.get("skipped_modules", {}))
        if r.get("skipped"):  # nothing importable
            n_skip += 1
            reasons = "; ".join(sorted(set(r["skipped_modules"].values())))
            print(f"{r['spec']:<32} {nproof:<6} {'0 (skip)':<7} SKIPPED ({reasons})")
            continue
        n_ok += 1
        if nskipmod:
            partial.append(r)
            print(f"{r['spec']:<32} {nproof:<6} {len(r['copied']):<7} ok ({nskipmod} module(s) skipped)")
        else:
            print(f"{r['spec']:<32} {nproof:<6} {len(r['copied']):<7} ok")
    print()
    print(f"imported: {n_ok}   skipped: {n_skip}   errors: {n_err}")
    if partial:
        print("\nPartially imported (some proof modules skipped):")
        for r in partial:
            for m, why in sorted(r["skipped_modules"].items()):
                print(f"  - {r['spec']}/{m}: {why}")
    if n_skip:
        print("\nFully skipped:")
        for r in reports:
            if r.get("skipped"):
                reasons = "; ".join(sorted(set(r["skipped_modules"].values())))
                print(f"  - {r['spec']}: {reasons}")


if __name__ == "__main__":
    main()
