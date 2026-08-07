#!/usr/bin/env python3
"""Compute structural-complexity metrics for Proof Completion tasks.

Metrics (per task, from the *reference* human proof):
  1. reference_proof_steps — explicit TLAPS `<n>` step lines; Direct if none
  2. max_proof_depth — deepest `<n>` level (0 for Direct)
  3. transitive_proof_deps — distinct user-defined ops/theorems reachable from
     facts/defs cited by the reference proof (seeded from BY/USE/DEF text,
     closed over SANY op-refs + each cited theorem's own proof citations)
  4. reference_obligations — leaf obligations from `tlapm --summary` on the
     layered task with the reference proof ported in

Usage:
  uv run python scripts/structural_complexity_pc.py
  uv run python scripts/structural_complexity_pc.py --skip-obligations
  uv run python scripts/structural_complexity_pc.py --limit 20
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict, dataclass, field
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from common.validate import port_proof_to_benchmark  # noqa: E402
from dataset.proof_completion.generate import (  # noqa: E402
    get_theorem_proof_lines,
    parse_theorems,
)
from tlacore.sany.dump import dump_raw  # noqa: E402

BENCH_DIR = PROJECT_ROOT / "benchmark" / "proof-completion"
SOURCE_DIR = PROJECT_ROOT / "source"
OUT_DIR = PROJECT_ROOT / "analysis" / "structural-complexity"
MANIFEST_PATH = BENCH_DIR / "manifest.json"

TLAPM = Path(os.environ.get("TLAPM", Path.home() / ".tlapm" / "bin" / "tlapm"))
TLAPM_LIB = Path(os.environ.get("TLAPM_LIB", Path.home() / ".tlapm" / "lib" / "tlapm" / "stdlib"))
COMMUNITY_LIB = PROJECT_ROOT / "lib" / "community"

STEP_LINE_RE = re.compile(r"^[ \t]*<(\d+)>")
# Proof-step / citation noise to drop from BY/USE fact lists.
BACKENDS = {
    "OBVIOUS",
    "OMITTED",
    "TRUE",
    "FALSE",
    "SMT",
    "Z3",
    "Zenon",
    "Isa",
    "Isabelle",
    "Crush",
    "LS4",
    "SimpleSolver",
    "Superforce",
    "Tautology",
    "Only",
    "ONLY",
    "PTL",
    "NoSMTTZ",
}
STEP_REF_RE = re.compile(r"^<\d+>")


@dataclass
class TaskMetrics:
    task: str
    theorem: str | None = None
    source_file: str | None = None
    proof_found: bool = False
    # steps: None => missing proof; "Direct" encoded via steps_kind
    steps: int | None = None
    steps_kind: str | None = None  # "Direct" | "Structured" | None
    max_depth: int | None = None
    transitive_deps: int | None = None
    deps_seed_size: int | None = None
    deps_error: str | None = None
    obligations: int | None = None
    obligations_error: str | None = None
    composer_gt_proof_steps: int | None = None
    composer_verdict: str | None = None
    notes: list[str] = field(default_factory=list)


def strip_block_and_line_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    in_block = False
    while i < n:
        if not in_block and text.startswith("(*", i):
            in_block = True
            i += 2
            continue
        if in_block:
            if text.startswith("*)", i):
                in_block = False
                i += 2
            else:
                i += 1
            continue
        if text.startswith("\\*", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def count_steps_and_depth(proof_lines: list[str]) -> tuple[int, int]:
    clean = strip_block_and_line_comments("\n".join(proof_lines))
    steps = 0
    depth = 0
    for line in clean.splitlines():
        m = STEP_LINE_RE.match(line)
        if m:
            steps += 1
            depth = max(depth, int(m.group(1)))
    return steps, depth


_CITATION_SPLIT = re.compile(r"(?i)\b(?:PROOF\s+)?(?:BY|USE)\b|\bDEFS?\b|\bHIDE\b|\bOBVIOUS\b|\bOMITTED\b")


def _split_ident_list(blob: str) -> list[str]:
    """Split a BY/DEF argument list into identifiers (best-effort)."""
    blob = strip_block_and_line_comments(blob)
    # Drop nested proof-step bangs like <1>1!2
    blob = re.sub(r"<\d+>[A-Za-z0-9]*[!]?[A-Za-z0-9]*", " ", blob)
    # Keep Module!Op as a single token then take the Op side for matching.
    parts = re.split(r"[,]", blob)
    names: list[str] = []
    for p in parts:
        p = p.strip()
        if not p:
            continue
        # Take trailing identifier / qualified name tokens.
        for tok in re.findall(r"[A-Za-z_][\w]*(?:![A-Za-z_][\w]*)*", p):
            if "!" in tok:
                tok = tok.split("!")[-1]
            if tok in BACKENDS or STEP_REF_RE.match(tok):
                continue
            if tok.upper() in {b.upper() for b in BACKENDS}:
                continue
            names.append(tok)
    return names


def extract_proof_citations(proof_lines: list[str]) -> set[str]:
    """Names cited via BY/USE facts or DEF/DEFS in a proof body."""
    text = strip_block_and_line_comments("\n".join(proof_lines))
    cited: set[str] = set()
    # Walk line-joined text; citation clauses may wrap lines.
    # Match BY/USE ... (optional DEF/DEFS ...) up to end of "clause"
    # Heuristic: from BY/USE to end of line-group until next step or blank-ish.
    i = 0
    lines = text.splitlines()
    while i < len(lines):
        line = lines[i]
        # Gather a physical clause starting at BY/USE/PROOF BY
        m = re.search(r"(?i)\b(?:PROOF\s+)?(?:BY|USE)\b(.*)$", line)
        if not m:
            i += 1
            continue
        blob = m.group(1)
        j = i + 1
        # Continue while indented continuation (no new step / theorem)
        while j < len(lines):
            nxt = lines[j]
            if re.match(r"^[ \t]*<\d+>", nxt):
                break
            if re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\b", nxt.strip()):
                break
            if not nxt.strip():
                break
            # stop if a new BY/USE starts
            if re.search(r"(?i)(?:^|\s)(?:PROOF\s+)?(?:BY|USE)\b", nxt) and not nxt.strip().startswith(","):
                break
            blob += " " + nxt
            j += 1
        # Split facts vs defs
        def_m = re.search(r"(?i)\bDEFS?\b(.*)$", blob)
        if def_m:
            facts_blob = blob[: def_m.start()]
            defs_blob = def_m.group(1)
            # Truncate defs at another BY if any
            defs_blob = re.split(r"(?i)\b(?:BY|USE)\b", defs_blob)[0]
            cited.update(_split_ident_list(facts_blob))
            cited.update(_split_ident_list(defs_blob))
        else:
            cited.update(_split_ident_list(blob))
        i = j if j > i else i + 1
    return cited


def load_manifest() -> dict[str, dict]:
    return json.loads(MANIFEST_PATH.read_text())


def index_source_files() -> dict[str, list[Path]]:
    idx: dict[str, list[Path]] = defaultdict(list)
    for p in SOURCE_DIR.rglob("*.tla"):
        rel = p.relative_to(SOURCE_DIR)
        idx[rel.parts[0]].append(p)
    return idx


def target_theorem_name(task_path: Path) -> str | None:
    lines = task_path.read_text(encoding="utf-8", errors="ignore").split("\n")
    for line in reversed(lines):
        m = re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(\w+)\s*==", line.strip())
        if m:
            return m.group(2)
    return None


def find_reference_proof(task_key: str, source_index: dict[str, list[Path]]) -> tuple[str, list[str], Path] | None:
    """Return (theorem, proof_lines, source_path) or None."""
    module_dir = task_key.split("/")[0]
    name_no_ext = Path(task_key).stem
    thm = target_theorem_name(BENCH_DIR / task_key)
    if not thm:
        return None
    candidates: list[Path] = []
    for p in source_index.get(module_dir, []):
        if name_no_ext.startswith(p.stem + "_"):
            candidates.insert(0, p)
        else:
            candidates.append(p)
    for src in candidates:
        src_lines = src.read_text(encoding="utf-8", errors="ignore").split("\n")
        for sthm in parse_theorems(src_lines):
            if sthm.name == thm and sthm.has_proof:
                proof_lines = get_theorem_proof_lines(src_lines, sthm)
                while proof_lines and not proof_lines[-1].strip():
                    proof_lines.pop()
                # Drop trailing comment-only blocks that parse_theorems may include
                while proof_lines:
                    t = proof_lines[-1].strip()
                    if not t or t.startswith("(*") or t.startswith("\\*"):
                        proof_lines.pop()
                        continue
                    break
                return thm, proof_lines, src
    return None


@dataclass
class ExampleGraph:
    """User-defined ops/theorems and citation edges for a source closure."""

    operators: set[str] = field(default_factory=set)
    theorems: set[str] = field(default_factory=set)
    op_refs: dict[str, set[str]] = field(default_factory=lambda: defaultdict(set))
    # theorem -> names cited in its proof (facts+defs)
    thm_cites: dict[str, set[str]] = field(default_factory=lambda: defaultdict(set))
    dump_errors: list[str] = field(default_factory=list)


_EXTENDS_RE = re.compile(r"(?m)^EXTENDS\s+(.+)$")
_INSTANCE_RE = re.compile(r"\bINSTANCE\s+(\w+)")


def local_module_closure(root: Path, source_index: dict[str, list[Path]]) -> list[Path]:
    """root plus local EXTENDS/INSTANCE modules under the same example dir."""
    example = root.relative_to(SOURCE_DIR).parts[0]
    by_stem = {p.stem: p for p in source_index.get(example, [])}
    seen: set[Path] = set()
    order: list[Path] = []
    stack = [root]
    while stack:
        path = stack.pop()
        if path in seen:
            continue
        seen.add(path)
        order.append(path)
        try:
            text = strip_block_and_line_comments(path.read_text(encoding="utf-8", errors="ignore"))
        except OSError:
            continue
        mods: set[str] = set()
        for m in _EXTENDS_RE.finditer(text):
            for part in m.group(1).split(","):
                name = part.strip().split()[0] if part.strip() else ""
                if name:
                    mods.add(name)
        for m in _INSTANCE_RE.finditer(text):
            mods.add(m.group(1))
        for name in mods:
            dep = by_stem.get(name)
            if dep is not None and dep not in seen:
                stack.append(dep)
    return order


def build_example_graph(example: str, files: list[Path]) -> ExampleGraph:
    g = ExampleGraph()
    for path in files:
        # Theorem cite map from text (always)
        try:
            lines = path.read_text(encoding="utf-8", errors="ignore").split("\n")
        except OSError as e:
            g.dump_errors.append(f"{path}: read {e}")
            continue
        for thm in parse_theorems(lines):
            if not thm.name or thm.name.startswith("__unnamed_"):
                continue
            g.theorems.add(thm.name)
            if thm.has_proof:
                pl = get_theorem_proof_lines(lines, thm)
                g.thm_cites[thm.name] |= extract_proof_citations(pl)
        # SANY op graph
        try:
            raw = dump_raw(str(path), timeout=180)
        except Exception as e:  # noqa: BLE001 — investigation: keep going
            g.dump_errors.append(f"{path}: sany {e}")
            continue
        for o in raw.get("operators") or []:
            name = o.get("name")
            if not name:
                continue
            g.operators.add(name)
            for r in o.get("references") or []:
                g.op_refs[name].add(r)
        for t in raw.get("theorems") or []:
            name = t.get("name")
            if name:
                g.theorems.add(name)
    return g


def transitive_deps(seed: set[str], graph: ExampleGraph) -> set[str]:
    """User-defined ops/theorems reachable from seed citations."""
    user = graph.operators | graph.theorems
    frontier = [n for n in seed if n in user]
    seen: set[str] = set()
    while frontier:
        name = frontier.pop()
        if name in seen:
            continue
        seen.add(name)
        if name in graph.operators:
            for r in graph.op_refs.get(name, ()):
                if r in user and r not in seen:
                    frontier.append(r)
        if name in graph.theorems:
            for r in graph.thm_cites.get(name, ()):
                if r in user and r not in seen:
                    frontier.append(r)
            # Also follow definitional deps of names that are both? no-op
    return seen


def _obligations_worker(args: tuple) -> tuple[str, int | None, str | None]:
    task_key, proof_lines, context_rels, timeout = args
    tmp = tempfile.mkdtemp(prefix="pc_obl_")
    try:
        for rel in context_rels:
            src = BENCH_DIR / rel
            if src.is_file():
                shutil.copy2(src, Path(tmp) / src.name)
        task_path = BENCH_DIR / task_key
        ported = port_proof_to_benchmark(str(task_path), proof_lines)
        out_file = Path(tmp) / task_path.name
        out_file.write_text(ported)
        cmd = [str(TLAPM), "--summary", "-I", str(TLAPM_LIB)]
        if COMMUNITY_LIB.is_dir():
            cmd += ["-I", str(COMMUNITY_LIB)]
        cmd.append(task_path.name)
        try:
            proc = subprocess.run(
                cmd,
                cwd=tmp,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return task_key, None, f"timeout after {timeout}s"
        text = (proc.stdout or "") + "\n" + (proc.stderr or "")
        m = re.search(r"obligations_count\s*=\s*(\d+)", text)
        if not m:
            return task_key, None, f"no obligations_count (exit {proc.returncode})"
        return task_key, int(m.group(1)), None
    except Exception as e:  # noqa: BLE001
        return task_key, None, str(e)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def load_composer() -> dict[str, dict]:
    path = Path("/Users/mahdiya/UIUC Summer Program/TlapsBench-website/composer-2.5-proof-completion/results.json")
    if not path.is_file():
        return {}
    data = json.loads(path.read_text())
    out = {}
    for t in data.get("tasks") or []:
        key = t["task"] + ".tla"
        out[key] = t
    return out


def percentile(xs: list[float], p: float) -> float:
    if not xs:
        return float("nan")
    ys = sorted(xs)
    k = (len(ys) - 1) * p
    f = int(k)
    c = min(f + 1, len(ys) - 1)
    if f == c:
        return float(ys[f])
    return ys[f] + (ys[c] - ys[f]) * (k - f)


def summarize_numeric(name: str, values: list[int | float], direct_count: int = 0) -> dict:
    if not values and not direct_count:
        return {"metric": name, "n": 0}
    return {
        "metric": name,
        "n": len(values),
        "direct_or_zero_special": direct_count,
        "min": min(values) if values else None,
        "p25": percentile(values, 0.25) if values else None,
        "p50": percentile(values, 0.50) if values else None,
        "p75": percentile(values, 0.75) if values else None,
        "p90": percentile(values, 0.90) if values else None,
        "p95": percentile(values, 0.95) if values else None,
        "max": max(values) if values else None,
        "mean": statistics.fmean(values) if values else None,
    }


def spearman(x: list[float], y: list[float]) -> float:
    """Spearman rank correlation; ties get average ranks."""

    def ranks(a: list[float]) -> list[float]:
        order = sorted(range(len(a)), key=lambda i: a[i])
        r = [0.0] * len(a)
        i = 0
        while i < len(a):
            j = i
            while j + 1 < len(a) and a[order[j + 1]] == a[order[i]]:
                j += 1
            avg = (i + j) / 2.0 + 1.0
            for k in range(i, j + 1):
                r[order[k]] = avg
            i = j + 1
        return r

    if len(x) < 2:
        return float("nan")
    rx, ry = ranks(x), ranks(y)
    mx = statistics.fmean(rx)
    my = statistics.fmean(ry)
    num = sum((a - mx) * (b - my) for a, b in zip(rx, ry, strict=True))
    denx = sum((a - mx) ** 2 for a in rx) ** 0.5
    deny = sum((b - my) ** 2 for b in ry) ** 0.5
    if denx == 0 or deny == 0:
        return float("nan")
    return num / (denx * deny)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=0, help="Only first N manifest tasks")
    ap.add_argument("--skip-obligations", action="store_true")
    ap.add_argument("--skip-sany", action="store_true", help="Deps: seed size only, no closure")
    ap.add_argument("--obl-timeout", type=int, default=180)
    ap.add_argument("--obl-workers", type=int, default=6)
    ap.add_argument("--examples", type=str, default="", help="Comma-separated example dirs")
    args = ap.parse_args()

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    manifest = load_manifest()
    tasks = sorted(manifest)
    if args.examples:
        allow = {e.strip() for e in args.examples.split(",") if e.strip()}
        tasks = [t for t in tasks if t.split("/")[0] in allow]
    if args.limit:
        tasks = tasks[: args.limit]

    source_index = index_source_files()
    composer = load_composer()

    print(f"Tasks: {len(tasks)} (manifest {len(manifest)})")
    t0 = time.time()

    # --- Pass 1: locate proofs, steps, depth, citation seeds ---
    rows: dict[str, TaskMetrics] = {}
    proof_by_task: dict[str, list[str]] = {}
    source_path_by_task: dict[str, Path] = {}
    seeds: dict[str, set[str]] = {}
    sources_needed: set[Path] = set()

    for task_key in tasks:
        m = TaskMetrics(task=task_key)
        ct = composer.get(task_key)
        if ct:
            m.composer_gt_proof_steps = ct.get("gt_proof_steps")
            m.composer_verdict = ct.get("verdict")
        found = find_reference_proof(task_key, source_index)
        if not found:
            m.notes.append("no_reference_proof")
            rows[task_key] = m
            continue
        thm, proof_lines, src = found
        m.proof_found = True
        m.theorem = thm
        m.source_file = str(src.relative_to(PROJECT_ROOT))
        steps, depth = count_steps_and_depth(proof_lines)
        if steps == 0:
            m.steps = 0
            m.steps_kind = "Direct"
            m.max_depth = 0
        else:
            m.steps = steps
            m.steps_kind = "Structured"
            m.max_depth = depth
        seed = extract_proof_citations(proof_lines)
        seeds[task_key] = seed
        m.deps_seed_size = len(seed)
        proof_by_task[task_key] = proof_lines
        source_path_by_task[task_key] = src
        sources_needed.add(src)
        rows[task_key] = m

    print(f"Pass 1 done in {time.time() - t0:.1f}s; proofs found {sum(1 for r in rows.values() if r.proof_found)}")

    # --- Pass 2: SANY graphs scoped per source file (avoid cross-file name merge) ---
    graphs: dict[str, ExampleGraph] = {}
    if not args.skip_sany:
        sources = sorted(sources_needed)
        print(f"Building SANY graphs for {len(sources)} source closures...")
        for i, src in enumerate(sources, 1):
            files = local_module_closure(src, source_index)
            print(
                f"  [{i}/{len(sources)}] {src.relative_to(PROJECT_ROOT)} (+{len(files) - 1} local deps)",
                flush=True,
            )
            graphs[str(src)] = build_example_graph(src.relative_to(SOURCE_DIR).parts[0], files)
        for task_key, m in rows.items():
            if not m.proof_found:
                continue
            src = source_path_by_task[task_key]
            g = graphs.get(str(src))
            if not g:
                m.deps_error = "no_graph"
                continue
            try:
                closure = transitive_deps(seeds.get(task_key, set()), g)
                m.transitive_deps = len(closure)
            except Exception as e:  # noqa: BLE001
                m.deps_error = str(e)
    else:
        for _task_key, m in rows.items():
            if m.proof_found:
                m.transitive_deps = m.deps_seed_size
                m.notes.append("deps_seed_only")
    # --- Pass 3: obligations ---
    if not args.skip_obligations:
        jobs = []
        for task_key, m in rows.items():
            if not m.proof_found:
                continue
            ctx = list(manifest[task_key].get("context") or [])
            jobs.append((task_key, proof_by_task[task_key], ctx, args.obl_timeout))
        print(f"Computing obligations for {len(jobs)} tasks with {args.obl_workers} workers...")
        done = 0
        with ProcessPoolExecutor(max_workers=args.obl_workers) as ex:
            futs = {ex.submit(_obligations_worker, j): j[0] for j in jobs}
            for fut in as_completed(futs):
                task_key, obl, err = fut.result()
                rows[task_key].obligations = obl
                rows[task_key].obligations_error = err
                done += 1
                if done % 25 == 0 or done == len(jobs):
                    print(f"  obligations {done}/{len(jobs)}", flush=True)

    # --- Write outputs ---
    all_rows = [rows[k] for k in tasks]
    json_path = OUT_DIR / "metrics.json"
    json_path.write_text(json.dumps([asdict(r) for r in all_rows], indent=2) + "\n")

    csv_path = OUT_DIR / "metrics.csv"
    fields = [
        "task",
        "theorem",
        "source_file",
        "proof_found",
        "steps_kind",
        "steps",
        "max_depth",
        "transitive_deps",
        "deps_seed_size",
        "obligations",
        "composer_gt_proof_steps",
        "composer_verdict",
        "deps_error",
        "obligations_error",
    ]
    with csv_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        for r in all_rows:
            w.writerow(asdict(r))

    # Distributions
    structured_steps = [r.steps for r in all_rows if r.steps_kind == "Structured" and r.steps is not None]
    direct_n = sum(1 for r in all_rows if r.steps_kind == "Direct")
    depths = [r.max_depth for r in all_rows if r.steps_kind == "Structured" and r.max_depth is not None]
    deps = [r.transitive_deps for r in all_rows if r.transitive_deps is not None]
    obls = [r.obligations for r in all_rows if r.obligations is not None]

    depth_hist = Counter(depths)
    steps_bands = Counter()
    for s in structured_steps:
        if s <= 4:
            steps_bands["1-4"] += 1
        elif s <= 12:
            steps_bands["5-12"] += 1
        elif s <= 30:
            steps_bands["13-30"] += 1
        elif s <= 50:
            steps_bands["31-50"] += 1
        elif s <= 100:
            steps_bands["51-100"] += 1
        else:
            steps_bands["101+"] += 1

    # Correlations on tasks with all four
    complete = [
        r
        for r in all_rows
        if r.steps_kind == "Structured"
        and r.steps is not None
        and r.max_depth is not None
        and r.transitive_deps is not None
        and r.obligations is not None
    ]
    corr = {}
    if len(complete) >= 5:
        series = {
            "steps": [float(r.steps) for r in complete],
            "depth": [float(r.max_depth) for r in complete],
            "deps": [float(r.transitive_deps) for r in complete],
            "obligations": [float(r.obligations) for r in complete],
        }
        keys = list(series)
        for i, a in enumerate(keys):
            for b in keys[i + 1 :]:
                corr[f"{a}_vs_{b}"] = spearman(series[a], series[b])

    # Composer trend: pass rate by metric bands
    composer_trends = {}
    with_c = [r for r in all_rows if r.composer_verdict in ("PASS", "FAIL", "CHEATING")]
    if with_c:

        def band_steps(r: TaskMetrics) -> str:
            if r.steps_kind == "Direct":
                return "Direct"
            s = r.steps or 0
            if s <= 4:
                return "1-4"
            if s <= 12:
                return "5-12"
            if s <= 30:
                return "13-30"
            return "31+"

        def band_depth(r: TaskMetrics) -> str:
            if r.steps_kind == "Direct":
                return "Direct"
            d = r.max_depth or 0
            if d <= 1:
                return "1"
            if d == 2:
                return "2"
            if d == 3:
                return "3"
            return "4+"

        def band_deps(r: TaskMetrics) -> str:
            if r.transitive_deps is None:
                return "missing"
            d = r.transitive_deps
            if d <= 2:
                return "0-2"
            if d <= 8:
                return "3-8"
            if d <= 20:
                return "9-20"
            return "21+"

        def band_obl(r: TaskMetrics) -> str:
            if r.obligations is None:
                return "missing"
            o = r.obligations
            if o <= 1:
                return "0-1"
            if o <= 4:
                return "2-4"
            if o <= 12:
                return "5-12"
            return "13+"

        for label, bfn in [
            ("by_steps", band_steps),
            ("by_depth", band_depth),
            ("by_deps", band_deps),
            ("by_obligations", band_obl),
        ]:
            buckets: dict[str, list[TaskMetrics]] = defaultdict(list)
            for r in with_c:
                buckets[bfn(r)].append(r)
            composer_trends[label] = {
                b: {
                    "n": len(rs),
                    "pass_rate": sum(1 for r in rs if r.composer_verdict == "PASS") / len(rs),
                }
                for b, rs in sorted(buckets.items())
                if rs
            }

    # Residual usefulness: among same steps band, does deps/obl vary with pass?
    residual = {}
    if with_c:
        for band_name, bfn in [("steps", band_steps), ("depth", band_depth)]:
            residual[band_name] = {}
            buckets = defaultdict(list)
            for r in with_c:
                if r.transitive_deps is None or r.obligations is None:
                    continue
                buckets[bfn(r)].append(r)
            for b, rs in buckets.items():
                if len(rs) < 8:
                    continue
                passes = [r for r in rs if r.composer_verdict == "PASS"]
                fails = [r for r in rs if r.composer_verdict != "PASS"]
                if not passes or not fails:
                    continue
                residual[band_name][b] = {
                    "n_pass": len(passes),
                    "n_fail": len(fails),
                    "deps_mean_pass": statistics.fmean(r.transitive_deps for r in passes),
                    "deps_mean_fail": statistics.fmean(r.transitive_deps for r in fails),
                    "obl_mean_pass": statistics.fmean(r.obligations for r in passes),
                    "obl_mean_fail": statistics.fmean(r.obligations for r in fails),
                }

    summary = {
        "manifest_tasks": len(manifest),
        "computed_tasks": len(tasks),
        "proof_found": sum(1 for r in all_rows if r.proof_found),
        "proof_missing": sum(1 for r in all_rows if not r.proof_found),
        "direct_proofs": direct_n,
        "structured_proofs": len(structured_steps),
        "obligations_present": len(obls),
        "obligations_missing": sum(1 for r in all_rows if r.proof_found and r.obligations is None),
        "deps_present": len(deps),
        "deps_errors": sum(1 for r in all_rows if r.deps_error),
        "sany_dump_errors": {
            (str(Path(k).relative_to(PROJECT_ROOT)) if Path(k).is_absolute() else k): g.dump_errors
            for k, g in graphs.items()
            if g.dump_errors
        },
        "distributions": {
            "steps_structured": summarize_numeric("steps", structured_steps, direct_n),
            "steps_bands": {"Direct": direct_n, **dict(steps_bands)},
            "max_depth": summarize_numeric("max_depth", depths),
            "depth_hist": dict(sorted(depth_hist.items())),
            "transitive_deps": summarize_numeric("transitive_deps", deps),
            "obligations": summarize_numeric("obligations", obls),
        },
        "spearman_structured_complete": corr,
        "n_structured_complete": len(complete),
        "composer_overlap": len(with_c),
        "composer_trends": composer_trends,
        "residual_within_bands": residual,
        "composer_steps_agreement": None,
    }

    # Agreement with composer gt_proof_steps
    agree = 0
    compared = 0
    for r in all_rows:
        if r.composer_gt_proof_steps is None or not r.proof_found or r.steps is None:
            continue
        compared += 1
        # Composer used 0 for Direct
        if r.steps == r.composer_gt_proof_steps:
            agree += 1
    summary["composer_steps_agreement"] = {"compared": compared, "equal": agree}

    (OUT_DIR / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    # Markdown report skeleton
    md = []
    md.append("# Proof Completion structural-complexity metrics\n")
    md.append(f"Manifest tasks: **{len(manifest)}**; computed: **{len(tasks)}**.\n")
    md.append("## Coverage\n")
    md.append(f"- Reference proof found: {summary['proof_found']}")
    md.append(f"- Missing proof: {summary['proof_missing']}")
    md.append(f"- Direct (no numbered steps): {direct_n}")
    md.append(f"- Structured: {len(structured_steps)}")
    md.append(f"- Obligations computed: {len(obls)}")
    md.append(f"- Deps computed: {len(deps)}\n")
    md.append("## Distributions\n")
    md.append("### Reference proof steps\n")
    md.append(f"Bands: `{summary['distributions']['steps_bands']}`\n")
    md.append(f"Structured summary: `{summary['distributions']['steps_structured']}`\n")
    md.append("### Max proof depth\n")
    md.append(f"Hist: `{summary['distributions']['depth_hist']}`\n")
    md.append(f"Summary: `{summary['distributions']['max_depth']}`\n")
    md.append("### Transitive proof dependencies\n")
    md.append(f"`{summary['distributions']['transitive_deps']}`\n")
    md.append("### Reference proof obligations\n")
    md.append(f"`{summary['distributions']['obligations']}`\n")
    md.append("## Spearman (structured tasks with all metrics)\n")
    md.append(f"n={len(complete)} corr=`{corr}`\n")
    md.append("## Composer 2.5 pass-rate trends\n")
    md.append(f"```json\n{json.dumps(composer_trends, indent=2)}\n```\n")
    md.append("## Residual signal within steps/depth bands\n")
    md.append(f"```json\n{json.dumps(residual, indent=2)}\n```\n")
    (OUT_DIR / "report.md").write_text("\n".join(md) + "\n")

    print(json.dumps(summary, indent=2)[:4000])
    print(f"\nWrote {json_path}")
    print(f"Wrote {csv_path}")
    print(f"Wrote {OUT_DIR / 'summary.json'}")
    print(f"Wrote {OUT_DIR / 'report.md'}")
    print(f"Total time {time.time() - t0:.1f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
