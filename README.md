# TLAPS Proof Benchmark

A benchmark for evaluating AI's ability to write [TLAPS](https://proofs.tlaplus.net/doc/) (TLA+ Proof System) proofs.

## Overview

This benchmark evaluates an AI's ability to write machine-checked TLAPS proofs
for TLA+ theorems. Each task presents a TLA+ theorem whose proof body is replaced
by `PROOF OBVIOUS`; the AI must replace it with a real proof that `tlapm` accepts.

The benchmark comes in two task types:

- **Proof completion** — the full scaffolding (inductive invariants, lemma
  decomposition, and preceding lemmas marked `PROOF OMITTED`) is given, and the
  AI fills in one target proof.
- **Proof from scratch** — only the model and the target theorem statement
  remain; the AI must invent the entire proof structure, including any helper
  lemmas.

### Benchmark problems

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

### Setup (Linux x86-64 / macOS arm64)

Native setup runs on Linux x86-64 and macOS arm64 (Apple Silicon). Intel Macs
are unsupported — upstream tlapm publishes no x86-64 macOS binary.

Native setup requires GNU Make, `curl`, `tar`, [uv](https://docs.astral.sh/uv/),
and a JDK 21 or newer (`java` and `javac`). The project itself requires Python
≥ 3.12; `uv` selects or installs a compatible Python automatically.

On macOS, Homebrew's `openjdk` is keg-only, so `brew install openjdk@21` does not
by itself put `java`/`javac` on `PATH`. Register it once (no `sudo` needed) so it
becomes the default JDK:

```bash
brew install openjdk@21
ln -sfn "$(brew --prefix)/opt/openjdk@21/libexec/openjdk.jdk" \
  ~/Library/Java/JavaVirtualMachines/openjdk-21.jdk
```

From the repository root, run:

```bash
make setup
```

This one idempotent command syncs the locked Python environment, installs the
pinned tlapm/Apalache/SANY dependencies (the platform-matching tlapm binary is
selected automatically), compiles the SANY semantic dumper, builds
`check_proof_bin`, and runs a fast SANY smoke test. It is safe to rerun. Missing
system prerequisites and a moved TLAPM rolling-release pin are reported as
actionable errors. Allow roughly 3 GB of free disk space: the first run
downloads an approximately 850 MB TLAPM archive and installs about 1.7 GB of
external tools.

`make setup` also installs a single `tlaps-bench` CLI with subcommands for every
operation below (`tlaps-bench --help` lists them; `tlaps-bench <command> --help`
shows a command's full flag set):

| Command | Does |
|---|---|
| `tlaps-bench run` | Run an agent backend on the benchmarks |
| `tlaps-bench check` | Check a single proof for correctness and cheating |
| `tlaps-bench validate` | Batch-validate the source proofs with tlapm |
| `tlaps-bench generate` | Generate benchmarks (`--mode auto-complete`/`synthesis-from-scratch`) |
| `tlaps-bench score` | Score results — pass rate & per-module breakdown from results.json |

Virtualenv activation is optional: run `source .venv/bin/activate` once so the
`tlaps-bench` command is on your `PATH`, or leave the venv inactive and prefix
each command below with `uv run` (e.g. `uv run tlaps-bench run --filter GCD_GCD3`).

### Run the benchmark

`make setup` builds the checker binary required by the runner. The runner is
`--backend` × `--mode` parameterised — pick one of each.

```bash
# Single benchmark, auto-complete, Codex (default backend, default mode)
tlaps-bench run --filter GCD_GCD3

# Full auto-complete run, Codex, 40 parallel, 2h timeout
tlaps-bench run --jobs 40 --timeout 7200

# Same on synthesis-from-scratch (proof from scratch)
tlaps-bench run --mode synthesis-from-scratch --jobs 40 --timeout 7200

# Claude Code backend on auto-complete (override the default model if you like)
tlaps-bench run --backend claude_code --jobs 40
tlaps-bench run --backend claude_code --model claude-sonnet-4-6 --jobs 40

# GitHub Copilot CLI backend on auto-complete (override the default model if you like)
tlaps-bench run --backend copilot --jobs 40
tlaps-bench run --backend copilot --model gpt-5.5 --jobs 40
```

`make setup` installs the pinned tlapm 1.6 pre-release at `~/.tlapm/`. Each run
also requires the relevant agent CLI on `PATH` — [OpenAI Codex CLI](https://github.com/openai/codex)
for `--backend codex`, [Claude Code](https://github.com/anthropics/claude-code) for
`--backend claude_code`, or [GitHub Copilot CLI](https://github.com/github/copilot-cli)
for `--backend copilot`.

A finished run writes `results.json` and `summary.md` (with the headline pass
rate) to the output directory. Use `--resume` with a fixed `--output-dir` to
skip benchmarks already recorded as PASS and rerun the rest, and `tlaps-bench
score` to (re)compute pass rates and compare runs.

### Run with Docker (recommended)

```bash
make setup
cd docker && bash build.sh
# Set the API key(s) your chosen backend needs:
#   OPENAI_API_KEY (or AZURE_OPENAI_API_KEY + AZURE_OPENAI_HOST) for codex
#   ANTHROPIC_API_KEY                                            for claude_code
#   COPILOT_GITHUB_TOKEN (or GH_TOKEN / GITHUB_TOKEN)            for copilot
docker-compose run bench python3 /scripts/runner.py --jobs 40                       # auto-complete + codex
docker-compose run bench python3 /scripts/runner.py --backend claude_code --mode synthesis-from-scratch --jobs 40
```

The container mounts the whole `benchmark/` tree. `make setup` prepares the
prebuilt checker and SANY assets consumed by `docker/build.sh`. Docker blocks
access to GitHub/TLA+ sites to prevent data leakage.

### Validate benchmarks

Verify that the source proofs (before `PROOF OBVIOUS` replacement) are valid:

```bash
# Validate all benchmarks (uses tlapm 1.6 pre-release by default)
tlaps-bench validate --jobs 40

# Validate with an alternative tlapm (e.g. 1.5) as a rerun for failures
tlaps-bench validate --jobs 40 --rerun --rerun-tlapm /path/to/tlapm15

# Filter specific benchmarks
tlaps-bench validate --filter Paxos --jobs 10
```

### Check a single proof

```bash
tlaps-bench check benchmark/auto-complete/Euclid/GCD_GCD3.tla [--mode auto-complete] [--tlapm PATH] [--timeout SECS]
tlaps-bench check benchmark/synthesis-from-scratch/Cantor/Cantor1_cantor.tla --mode synthesis-from-scratch
```

`--mode` controls which cheating rules apply: auto-complete enforces a byte-identical preamble (the agent only fills in the last proof); synthesis-from-scratch lets the agent add new lemmas above the target theorem. Both modes still reject `PROOF OMITTED`, new `AXIOM`/`ASSUME`, bare-QED tricks, and dependency-file tampering.

Exit codes: `0` = PASS, `1` = FAIL, `3` = ERROR. A detected cheat reports as FAIL (exit `1`).

### Generate benchmarks from source

```bash
tlaps-bench generate                       # auto-complete (default)
tlaps-bench generate --mode synthesis-from-scratch   # synthesis-from-scratch
```

Auto-complete extracts each theorem with a real proof, replaces the last proof with `PROOF OBVIOUS`, and writes one benchmark file per theorem to `benchmark/auto-complete/`. Use `--mode synthesis-from-scratch` to drive the synthesis-from-scratch generator instead.
