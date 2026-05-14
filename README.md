# TLAPS Proof Benchmark

A benchmark for evaluating AI's ability to write [TLAPS](https://proofs.tlaplus.net/doc/) (TLA+ Proof System) proofs.

## Overview

This benchmark contains **193 proof tasks** based on [hengxin/tlaps-examples](https://github.com/hengxin/tlaps-examples). Each task presents a TLA+ theorem with its proof body replaced by `PROOF OBVIOUS`, challenging the AI to fill in a valid, machine-checked proof.

The benchmark provides the full proof scaffolding — inductive invariants, lemma decomposition, and preceding theorems (marked `PROOF OMITTED`) are all given. The AI only needs to write the proof steps for one target theorem.

## Benchmark Structure

Each benchmark file contains:
- Module header, definitions, and imports (unmodifiable preamble)
- Supporting lemmas/theorems with `PROOF OMITTED` (available for reference)
- **One target theorem** with `PROOF OBVIOUS` (to be replaced with a real proof)

```
benchmark/
  Allocator/          # 10 tasks
  AtomicBakery/       # 8 tasks
  BubbleSort/         # 8 tasks
  ByzantinePaxos/     # 38 tasks
  Cantor/             # 11 tasks
  Consensus/          # 50 tasks
  Data/               # 37 tasks
  EWD840/             # 2 tasks
  Euclid/             # 9 tasks
  Paxos/              # 13 tasks
  SimpleMutex/        # 5 tasks
  Two-Phase/          # 2 tasks
```

## Anti-Cheating

`check_proof.py` validates each proof attempt:
- **Preamble integrity**: everything above `PROOF OBVIOUS` must be unchanged
- **No PROOF OMITTED / bare OMITTED**: proof obligations must not be skipped (with TLA+ comment stripping)
- **No AXIOM/ASSUME**: no new axioms in the proof section
- **No bare QED exploit**: detects `<n> QED` without `BY` via `tlapm --summary` (missing proof steps)
- **Dependency files**: other `.tla` files in the same directory must be unmodified

## Codex (GPT-5.5) Results

We evaluated [OpenAI Codex CLI](https://github.com/openai/codex) with GPT-5.5 on all 193 benchmarks. Each run was fully automated (`codex exec`, no human guidance) in a Docker container with only tlapm 1.5, the benchmark file, and `check_proof.py`. Website access to GitHub, Lamport's homepage, and TLA+ sites was blocked via DNS to prevent data leakage.

| Metric | Result |
|--------|--------|
| Pass | **186 / 193** (96.4%) |
| Fail | 3 |
| Cheating (detected) | 4 |
| Total proof obligations | 6,829 |
| Wall time (40 parallel) | ~2.5 h |
| Total tokens | 250M input / 1.5M output |

### Failed Benchmarks

| Benchmark | Obligations | Notes |
|-----------|-------------|-------|
| Consensus/PaxosProof_struct_lemma | 1/3 failed | Stuck on Phase1b/2b set reasoning |
| Paxos/Paxos_Invariant | 3/41 failed | Phase1b MsgInv' intractable; source also fails tlapm 1.5+1.6 |
| ByzantinePaxos/BPConProof_MsgsLemma | 3/123 failed | 2h timeout; 115/119 proved, still iterating at cutoff |

### Proof Anti-patterns Detected

Four benchmarks triggered anti-pattern detection — all are interesting case studies in how AI-generated proofs can contain unsound patterns that pass the checker. See [`PROOF_ANTIPATTERNS.md`](PROOF_ANTIPATTERNS.md) for a full catalog of known anti-patterns (observed and anticipated), detection mechanisms, countermeasures, and a detailed timeline of how Codex reverse-engineered the checker.

| Benchmark | Method |
|-----------|--------|
| Paxos/PaxosHistVar_Invariant | Deleted `PROOF` keyword → bare theorem declaration generates 0 obligations; added fake theorem to bypass zero-obligation check. Rerun also failed: tlapm 1.5 generates 0 obligations for this benchmark (source requires 1.6); tested on 1.6: 1/2 obligations failed. |
| ByzantinePaxos/VoteProof_Liveness | Used bare `<1> QED` (without BY) which generates 0 obligations for the QED step; reverse-engineered checker's zero-obligation detection from error messages. |
| Consensus/Consensus_IsBijectionTransitive | Used bare `<2> QED` (without BY) in the target proof — detected by `tlapm --summary` reporting missing proofs. |
| Paxos/Paxos_SafeAtStable | Used 8 bare QED steps (without BY) throughout the target proof — detected by `tlapm --summary` reporting missing proofs. |

Full results are in `results/codex/20260513_093531/`, with per-benchmark directories containing `benchmark.tla`, `solution.tla`, `codex_output.jsonl`, `transcript.txt`, and `check.result`.

## Scripts

| Script | Purpose |
|--------|---------|
| `run_codex_benchmark.py` | Run Codex (or any codex-compatible agent) on benchmarks |
| `validate_benchmarks.py` | Validate benchmark source proofs with tlapm |
| `check_proof.py` | Check a single proof attempt for correctness and cheating |
| `generate_benchmarks.py` | Generate benchmark files from source proofs (replaces last proof with `PROOF OBVIOUS`) |
| `cheating_detection.py` | Shared cheating detection logic (used by `check_proof.py` and `validate_benchmarks.py`) |

### Run Codex benchmark

```bash
# Single benchmark
python3 run_codex_benchmark.py --filter GCD_GCD3

# Full run (40 parallel, 2h timeout)
python3 run_codex_benchmark.py --jobs 40 --timeout 7200
```

Requires: [OpenAI Codex CLI](https://github.com/openai/codex) installed, tlapm 1.5 at `~/.tlapm15/` or `/tmp/tlapm15/`.

### Run with Docker (recommended)

```bash
cd docker && bash build.sh
# Set OPENAI_API_KEY or AZURE_OPENAI_API_KEY + AZURE_OPENAI_HOST
docker-compose run bench python3 /run_codex_benchmark.py --jobs 40
```

Docker blocks access to GitHub/TLA+ sites and removes tlapm's bundled examples directory to prevent data leakage.

### Validate benchmarks

Verify that the source proofs (before `PROOF OBVIOUS` replacement) are valid:

```bash
# Validate all benchmarks with tlapm 1.5
python3 validate_benchmarks.py --jobs 40

# Validate with tlapm 1.6 rerun for failures
python3 validate_benchmarks.py --jobs 40 --rerun --rerun-tlapm /path/to/tlapm16

# Filter specific benchmarks
python3 validate_benchmarks.py --filter Paxos --jobs 10
```

### Check a single proof

```bash
python3 check_proof.py benchmark/Euclid/GCD_GCD3.tla [--tlapm PATH] [--timeout SECS]
```

Exit codes: `0` = PASS, `1` = FAIL, `2` = CHEATING, `3` = ERROR.

### Generate benchmarks from source

```bash
python3 generate_benchmarks.py --source-dir /path/to/tlaps-examples --output-dir benchmark/
```

Extracts each theorem with a real proof, replaces the last proof with `PROOF OBVIOUS`, and writes one benchmark file per theorem.

## Related Work

- [tlaplus/Examples#211](https://github.com/tlaplus/Examples/pull/211) — Claude Opus 4.7 writes TLAPS proofs from bare specs (27 files, human-guided)
- [tlaplus/Examples#212](https://github.com/tlaplus/Examples/pull/212) — Claude Opus 4.7 + Apalache for TCP safety proof (5665 lines, human-guided)
- [verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis) — Similar benchmark methodology for Verus/Rust proof synthesis (Verus-Bench + VeruSAGE-Bench)
