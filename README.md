# TLAPS Proof Benchmark

A benchmark for evaluating AI's ability to write [TLAPS](https://proofs.tlaplus.net/doc/) (TLA+ Proof System) proofs.

## Overview

This benchmark contains **190 proof tasks** based on [hengxin/tlaps-examples](https://github.com/hengxin/tlaps-examples). Each task presents a TLA+ theorem with its proof body replaced by `PROOF OBVIOUS`, challenging the AI to fill in a valid, machine-checked proof.

The benchmark provides the full proof scaffolding — inductive invariants, lemma decomposition, and preceding theorems (marked `PROOF OMITTED`) are all given. The AI only needs to write the proof steps for one target theorem.

## Benchmark Structure

Each benchmark file contains:
- Module header, definitions, and imports (unmodifiable preamble)
- Supporting lemmas/theorems with `PROOF OMITTED` (available for reference)
- **One target theorem** with `PROOF OBVIOUS` (to be replaced with a real proof)

```
benchmark/
  Allocator/          # 10 tasks
  AtomicBakery/       # 17 tasks
  BubbleSort/         # 17 tasks
  ByzantinePaxos/     # 20 tasks
  Cantor/             # 4 tasks
  Consensus/          # 8 tasks
  Data/               # 7 tasks
  EWD840/             # 24 tasks
  Euclid/             # 3 tasks
  Paxos/              # 43 tasks
  SimpleMutex/        # 29 tasks
  Two-Phase/          # 8 tasks
```

## Anti-Cheating

`check_proof.py` validates each proof attempt:
- **Preamble integrity**: everything above `PROOF OBVIOUS` must be unchanged
- **No PROOF OMITTED / bare OMITTED**: proof obligations must not be skipped (with TLA+ comment stripping)
- **No AXIOM/ASSUME**: no new axioms in the proof section
- **Dependency files**: other `.tla` files in the same directory must be unmodified

## Codex (GPT-5.5) Results

We evaluated [OpenAI Codex CLI](https://github.com/openai/codex) with GPT-5.5 on all 190 benchmarks. Each run was fully automated (`codex exec`, no human guidance) in an isolated workspace with only tlapm 1.5, the benchmark file, and `check_proof.py`.

| Metric | Result |
|--------|--------|
| Pass | **189 / 190** |
| Fail | 0 |
| Cheating (detected) | 1 (VoteProof_Liveness) |
| Total proof lines | 6,267 |
| Avg proof lines | 33.0 |
| Wall time (40 parallel) | ~36 min |
| Total tokens | 178M input / 1.1M output |

The single failure (`VoteProof_Liveness`) is a complex liveness proof (`LiveSpec => C!LiveSpec`) involving temporal operators (`[]<>`, `~>`, `WF`). TLAPS has limited support for temporal reasoning — the original human-written proof also used `OMITTED` for this theorem. See [`codex_results/comparison.md`](codex_results/comparison.md) for a detailed comparison with original proofs.

Results are in `codex_results/20260512_222431/`, with per-benchmark directories containing `benchmark.tla`, `solution.tla`, `codex_output.jsonl`, `transcript.txt`, and `check.result`.

## Usage

### Check a proof

```bash
python3 check_proof.py benchmark/Euclid/GCD_GCD3.tla [--tlapm PATH] [--timeout SECS]
```

Exit codes: `0` = PASS, `1` = FAIL, `2` = CHEATING, `3` = ERROR.

### Run Codex benchmark

```bash
# Single benchmark
python3 run_codex_benchmark.py --filter GCD_GCD3

# Full run (40 parallel)
python3 run_codex_benchmark.py --jobs 40 --timeout 600
```

Requires: [OpenAI Codex CLI](https://github.com/openai/codex) installed, tlapm 1.5 at `~/.tlapm15/` or `/tmp/tlapm15/`.

## Related Work

- [tlaplus/Examples#211](https://github.com/tlaplus/Examples/pull/211) — Claude Opus 4.7 writes TLAPS proofs from bare specs (27 files, human-guided)
- [tlaplus/Examples#212](https://github.com/tlaplus/Examples/pull/212) — Claude Opus 4.7 + Apalache for TCP safety proof (5665 lines, human-guided)
- [verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis) — Similar benchmark methodology for Verus/Rust proof synthesis (Verus-Bench + VeruSAGE-Bench)
