# TLAPS Proof Benchmark

[![CI](https://github.com/specula-org/tlaps-bench/actions/workflows/ci.yml/badge.svg)](https://github.com/specula-org/tlaps-bench/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

A benchmark for evaluating AI's ability to write [TLAPS](https://proofs.tlaplus.net/doc/) (TLA+ Proof System) proofs.

## Overview

TLAPS proofs are checked mechanically by `tlapm`: a proof is either accepted or
rejected, with no partial credit and no room for a plausible-but-wrong argument.
That makes proof construction a sharp test of an AI's formal reasoning.

Each task presents a TLA+ theorem whose proof body is replaced by `PROOF OBVIOUS`;
the AI must replace it with a real proof that `tlapm` accepts. Tasks come in two
types:

- **Proof completion** (`--mode auto-complete`) — the full scaffolding (inductive
  invariants, lemma decomposition, and preceding lemmas marked `PROOF OMITTED`)
  is given, and the AI fills in one target proof.
- **Proof from scratch** (`--mode synthesis-from-scratch`) — only the model and
  the target theorem statement remain; the AI must invent the entire proof
  structure, including any helper lemmas.

## Benchmark problems

| Source | Proof completion | Proof from scratch | Total |
|---|--:|--:|--:|
| tlaplus/Examples | 381 | 126 | 507 |
| TLAPS distribution examples | 154 | 80 | 234 |
| ZooKeeper / Zab (Remix) | 0 | 18 | 18 |
| Ivy liveness | 0 | 12 | 12 |
| etcd (Specula) | 0 | 8 | 8 |
| AbstractRaft (Stephan Merz) | 0 | 4 | 4 |
| OpenAddressing (Markus Kuppe) | 1 | 5 | 6 |
| Anvil | 0 | 1 | 1 |
| **Total** | **536** | **254** | **790** |

## Running

Requirements: [uv](https://docs.astral.sh/uv/) and
[Docker](https://docs.docker.com/get-docker/).

```bash
git clone https://github.com/specula-org/tlaps-bench.git
cd tlaps-bench
export OPENAI_API_KEY=sk-...                 # Codex is the default backend
uv run tlaps-bench run --filter GCD_GCD3
```

The first run builds a sandbox Docker image (tlapm, SANY, and the proof checker
bundled in) and runs the task inside it — a firewall allows only the LLM API
hosts, and the benchmarks are mounted read-only. Later runs reuse the image.
Results land in `results/<mode>/<backend>/<timestamp>/`.

Scale up, or switch task type:

```bash
# Full proof-completion suite: 10 in parallel, 2h timeout each
uv run tlaps-bench run --jobs 10 --timeout 7200

# Proof from scratch
uv run tlaps-bench run --mode synthesis-from-scratch --jobs 10
```

Each run writes `results.json` and `summary.md` (with the headline pass rate);
`uv run tlaps-bench score` (re)computes and compares pass rates. Use `--resume`
with a fixed `--output-dir` to skip tasks already recorded as PASS, and
`--force-build` to rebuild the image after changing source.

Choosing an agent (`--backend` / `--model`) and its credentials, the full CLI
reference, and native (`--no-container`) setup are covered in the
[usage guide](docs/USAGE.md).

## License

MIT — see [`LICENSE`](LICENSE). Third-party benchmark sources are attributed in
[`NOTICE`](NOTICE).
