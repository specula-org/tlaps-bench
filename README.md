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
benchmark/level1/
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

## Codex (GPT-5.5) Results — Level 2

Level 2 strips every supporting lemma and proof scaffold, so the agent must invent the
whole proof structure from scratch (see the Level 2 generator below). We evaluated
[OpenAI Codex CLI](https://github.com/openai/codex) with GPT-5.5 on all 210 Level-2
benchmarks, fully automated (`codex exec`, no human guidance) against tlapm and the
stripped benchmark file. Numbers below are aggregated across runs (2026-05 to 2026-06);
per-run summaries and full solutions live in the private results repo.

| Metric | Result |
|--------|--------|
| Pass | **189 / 210** (90.0%) |
| Fail | 21 |
| Cheating (detected) | 0 |
| Proof obligations proved | 11,840+ |

### Failed Benchmarks

| Benchmark | Obligations | Notes |
|-----------|-------------|-------|
| Paxos/Paxos_Consistent | 1/1 failed | Monolithic consistency theorem; top-level obligation unproved |
| Paxos/Paxos_Invariant | 1/1 failed | Phase1b/2b inductive invariant intractable |
| Paxos/Paxos_Refinement | 1/1 failed | Refinement mapping to Consensus unproved |
| ByzantinePaxos/BPConProof_Inv | 1/1 failed | Byzantine Paxos main invariant |
| ByzantinePaxos/BPConProof_P_Spec | 1/1 failed | Byzantine Paxos spec-level proof |
| ByzantinePaxos/VoteProof_Liveness | 1/1 failed | Voting liveness theorem |
| ByzantinePaxos/VoteProof_VT2 | 1/1 failed | Voting theorem VT2 |
| byzpaxos/BPConProof_Invariance | 7/617 failed | Byzantine Paxos invariance (617 obligations) |
| byzpaxos/BPConProof_P_Spec | 16/119 failed | Byzantine Paxos P-spec |
| byzpaxos/VoteProof_VT3 | 3/128 failed | Voting theorem VT3 |
| TencentPaxos/TPaxosWithProof_Consistent | 5/107 failed | TencentPaxos consistency |
| TencentPaxos/TPaxosWithProof_Invariant | 4/156 failed | TencentPaxos invariant |
| barriers/Barriers_Invariant | 7/411 failed | Barrier inductive invariant |
| barriers/Barriers_FlushInvariant | 12/351 failed | Barrier flush invariant |
| barriers/Barriers_B_Spec | 3/139 failed | Stuck on inductive step `IndInv /\ [Next]_vars => IndInv'` (4h rerun still failed) |
| MultiCarElevator/Elevator_proof_SafetyCorrect | 10/137 failed | Stuck on `PeopleWaiting = WaitingAt` equivalence lemma (4h rerun still failed) |
| ewd998/EWD998_proof_TerminationDetectionInv | 5/443 failed | Termination-detection invariant |
| lamport_mutex/LamportMutex_proofs_BoundedNetworkInv | 6/180 failed | Bounded-network invariant |
| locks_auxiliary_vars/LockHS_P_Spec | 6/72 failed | Handshake-lock refinement |
| Bakery-Boulangerie/Boulanger_MutualExclusion | 11/222 failed | Boulangerie mutual exclusion |
| ivy_examples_tlb | 8/98 failed | TLB shootdown safety |

Failures concentrate in the hardest theorem classes — Byzantine/Tencent Paxos, barrier
and termination-detection inductive invariants, liveness, and refinement. Two tasks that
once hit the agent time limit (Elevator, Barriers_B_Spec) were re-run with a 4 h budget
and still failed, self-terminating well within the limit — these are model-limited, not
time-limited.

## Repo layout

```
src/
  dataset/level1/generate.py   Level 1 generator (proof-completion benchmarks)
  dataset/level2/generate.py   Level 2 generator (proof-from-scratch)
  dataset/level2/design.md     Design doc for the L2 generator
  dataset/sany-dump/           Java SANY semantic dumper (used by L2 generator)
  common/check_proof.py        Single-proof checker + cheating detection
  common/validate.py           Batch-validate source proofs with tlapm
  common/cheating_detection.py
  evaluator/runner.py          AI-agent runner (currently Codex CLI)
  evaluator/prompts/           Prompt templates per level
scripts/                       Install + convenience wrappers
benchmark/level1/              Generated L1 benchmarks (193 files)
benchmark/level2/              Generated L2 benchmarks
source/                        Original TLA+ specs used as input
lib/                           Vendored: tla2tools.jar (gitignored)
docker/                        Container build + isolation
```

### Setup (Linux x86-64)

Native setup requires GNU Make, `curl`, `tar`, [uv](https://docs.astral.sh/uv/),
and a JDK 21 or newer (`java` and `javac`). The project itself requires Python
≥ 3.12; `uv` selects or installs a compatible Python automatically.

From the repository root, run:

```bash
make setup
```

This one idempotent command syncs the locked Python environment, installs the
pinned tlapm/Apalache/SANY dependencies, compiles the SANY semantic dumper,
builds `check_proof_bin`, and runs a fast SANY smoke test. It is safe to rerun.
Missing system prerequisites and a moved TLAPM rolling-release pin are reported
as actionable errors. Allow roughly 3 GB of free disk space: the first run
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
| `tlaps-bench generate` | Generate benchmarks (`--level level1`/`level2`) |
| `tlaps-bench score` | Score / aggregate results (not implemented yet) |

Virtualenv activation is optional: run `source .venv/bin/activate` once so the
`tlaps-bench` command is on your `PATH`, or leave the venv inactive and prefix
each command below with `uv run` (e.g. `uv run tlaps-bench run --filter GCD_GCD3`).

### Run the benchmark

`make setup` builds the checker binary required by the runner. The runner is
`--backend` × `--level` parameterised — pick one of each.

```bash
# Single benchmark, L1, Codex (default backend, default level)
tlaps-bench run --filter GCD_GCD3

# Full L1 run, Codex, 40 parallel, 2h timeout
tlaps-bench run --jobs 40 --timeout 7200

# Same on L2 (proof from scratch)
tlaps-bench run --level level2 --jobs 40 --timeout 7200

# Claude Code backend on L1 (override the default model if you like)
tlaps-bench run --backend claude_code --jobs 40
tlaps-bench run --backend claude_code --model claude-sonnet-4-6 --jobs 40

# GitHub Copilot CLI backend on L1 (override the default model if you like)
tlaps-bench run --backend copilot --jobs 40
tlaps-bench run --backend copilot --model gpt-5.5 --jobs 40
```

`make setup` installs the pinned tlapm 1.6 pre-release at `~/.tlapm/`. Each run
also requires the relevant agent CLI on `PATH` — [OpenAI Codex CLI](https://github.com/openai/codex)
for `--backend codex`, [Claude Code](https://github.com/anthropics/claude-code) for
`--backend claude_code`, or [GitHub Copilot CLI](https://github.com/github/copilot-cli)
for `--backend copilot`.

### Usage monitoring & quota gate (Claude Max)

`scripts/usage.sh` queries the Claude OAuth usage endpoint (subscription auth
only) and reports the rolling-window utilization, mirroring Specula's monitor:

```bash
bash scripts/usage.sh              # full JSON from /api/oauth/usage
bash scripts/usage.sh --summary    # one human-readable line per window
bash scripts/usage.sh --check 80   # exit 1 if any 5h/7d window > 80%
```

When `--backend claude_code` runs on a Max subscription, the runner uses this
to **gate before launching each agent**: if 5h/7d usage is over threshold it
sleeps until the window's `resets_at` (+2 min), then resumes — so a long
parallel run pauses instead of failing when quota runs out.

```bash
# Defaults: pause at 5h>80% or 7d>95%, sleep through up to 6 resets.
tlaps-bench run --backend claude_code --jobs 40
# Tune thresholds, or set 0 to disable a window:
tlaps-bench run --backend claude_code --jobs 40 \
    --quota-5h 90 --quota-7d 95 --quota-max-waits 4
tlaps-bench run --backend claude_code --quota-5h 0 --quota-7d 0  # off
```

The gate fails open: it is skipped for `--backend codex`, and for API-key auth
(incl. Docker) where the OAuth usage endpoint and `~/.claude/.credentials.json`
token are absent — so it never blocks a run it can't measure.

### Run with Docker (recommended)

```bash
make setup
cd docker && bash build.sh
# Set the API key(s) your chosen backend needs:
#   OPENAI_API_KEY (or AZURE_OPENAI_API_KEY + AZURE_OPENAI_HOST) for codex
#   ANTHROPIC_API_KEY                                            for claude_code
#   COPILOT_GITHUB_TOKEN (or GH_TOKEN / GITHUB_TOKEN)            for copilot
docker-compose run bench python3 /scripts/runner.py --jobs 40                       # L1 + codex
docker-compose run bench python3 /scripts/runner.py --backend claude_code --level level2 --jobs 40
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
tlaps-bench check benchmark/level1/Euclid/GCD_GCD3.tla [--level 1] [--tlapm PATH] [--timeout SECS]
tlaps-bench check benchmark/level2/Cantor/Cantor1_cantor.tla --level 2
```

`--level` controls which cheating rules apply: L1 enforces a byte-identical preamble (the agent only fills in the last proof); L2 lets the agent add new lemmas above the target theorem. Both levels still reject `PROOF OMITTED`, new `AXIOM`/`ASSUME`, bare-QED tricks, and dependency-file tampering.

Exit codes: `0` = PASS, `1` = FAIL, `2` = CHEATING, `3` = ERROR.

### Generate benchmarks from source

```bash
tlaps-bench generate                  # Level 1 (default)
tlaps-bench generate --level level2   # Level 2 (proof from scratch)
```

Level 1 extracts each theorem with a real proof, replaces the last proof with `PROOF OBVIOUS`, and writes one benchmark file per theorem to `benchmark/level1/`. Use `--level level2` to drive the Level 2 generator instead.

## Related Work

- [tlaplus/Examples#211](https://github.com/tlaplus/Examples/pull/211) — Claude Opus 4.7 writes TLAPS proofs from bare specs (27 files, human-guided)
- [tlaplus/Examples#212](https://github.com/tlaplus/Examples/pull/212) — Claude Opus 4.7 + Apalache for TCP safety proof (5665 lines, human-guided)
- [verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis) — Similar benchmark methodology for Verus/Rust proof synthesis (Verus-Bench + VeruSAGE-Bench)
