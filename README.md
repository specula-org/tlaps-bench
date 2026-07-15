# TLAPS Proof Benchmark

[![CI](https://github.com/specula-org/tlaps-bench/actions/workflows/ci.yml/badge.svg)](https://github.com/specula-org/tlaps-bench/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

A benchmark for evaluating AI's ability to write [TLAPS](https://proofs.tlaplus.net/doc/) (TLA+ Proof System) proofs.

Benchmark results are available on the [TLAPS-Bench website](https://specula-org.github.io/tlaps-bench-website/).

## Overview

TLAPS proofs are checked mechanically by `tlapm`: a proof is either accepted or
rejected, with no partial credit and no room for a plausible-but-wrong argument.
That makes proof construction a sharp test of an AI's formal reasoning.

Each task presents a TLA+ theorem whose proof body is replaced by `PROOF OBVIOUS`;
the AI must replace it with a real proof that `tlapm` accepts. Tasks come in two
types:

- **Proof completion** (`--mode proof-completion`) — the full scaffolding (inductive
  invariants, lemma decomposition, and preceding lemmas marked `PROOF OMITTED`)
  is given, and the AI fills in one target proof.
- **Proof from scratch** (`--mode proof-from-scratch`) — only the model and
  the target theorem statement remain; the AI must invent the entire proof
  structure, including any helper lemmas.

## Benchmark problems

The benchmark draws on two kinds of source. A base of classic TLA+ **example
libraries**, a small set of **systems specifications** — real
protocols, several with no published proof. Both sets are expected to keep
growing as more specifications are added.
A `–` marks a source with no human proofs, from which no proof-completion task
can be derived.

**Example libraries**

| Source | Examples | Proof completion | Proof from scratch | Total |
|---|--:|--:|--:|--:|
| [tlaplus/Examples](https://github.com/tlaplus/Examples) | 45 | 379 | 126 | 505 |
| [TLAPS distribution examples](https://github.com/tlaplus/tlapm) | 14 | 103 | 57 | 160 |
| **Subtotal** | **59** | **482** | **183** | **665** |

**Systems specifications**

| Source | Examples | Proof completion | Proof from scratch | Total |
|---|--:|--:|--:|--:|
| [ZooKeeper (Remix)](https://arxiv.org/abs/2409.14301) | 2 | – | 18 | 18 |
| [Ivy liveness](https://github.com/kenmcmil/ivy) | 6 | – | 12 | 12 |
| [etcd (Specula)](https://github.com/specula-org) | 1 | – | 8 | 8 |
| [OpenAddressing](https://github.com/lemmy/Examples) | 1 | 1 | 5 | 6 |
| [two_thread_mutex (Anvil)](https://github.com/anvil-verifier/anvil/blob/main/src/tla_demo.rs) | 1 | – | 1 | 1 |
| **Subtotal** | **11** | **1** | **44** | **45** |

**70 examples, 710 tasks in total.** A per-example breakdown is in
[`docs/DATASET.md`](docs/DATASET.md).

## Running

Requirements: [uv](https://docs.astral.sh/uv/) and
[Docker](https://docs.docker.com/get-docker/).
Windows users should run the benchmark through WSL2; native Windows is not supported.

```bash
git clone https://github.com/specula-org/tlaps-bench.git
cd tlaps-bench
export OPENAI_API_KEY=sk-...        # This step is optional: Codex is the default backend if no OpenAI key is provided.
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
uv run tlaps-bench run --mode proof-from-scratch --jobs 10
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
