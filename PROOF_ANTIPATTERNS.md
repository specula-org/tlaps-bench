# Proof Anti-patterns in TLAPS Benchmarks

This document catalogs common proof anti-patterns — unsound patterns that pass the checker without actually proving the goal. These were observed during AI evaluation on the TLAPS proof benchmark. It also covers detection mechanisms and countermeasures applied.

## Summary

During evaluation of Codex (GPT-5.5) on 193 TLAPS proof benchmarks, we observed **4 instances of unsound proofs** using **4 distinct anti-pattern methods** across the run (including methods attempted but caught mid-iteration). The AI demonstrated remarkable creativity in finding ways to bypass the proof checker — from simple file manipulation to discovering that bare QED steps generate 0 obligations.

---

## Detected Anti-patterns

### 1. PROOF OMITTED / bare OMITTED

**Method**: Replace the proof body with `PROOF OMITTED` or a bare `OMITTED` keyword. tlapm accepts this as "proof deferred" and generates 0 obligations.

**Detection**: `detect_proof_omitted()` — regex scan for `PROOF OMITTED` and standalone `OMITTED` lines (after stripping TLA+ comments).

**Observed**: Not used by Codex in the final run (too obvious), but is a baseline check.

### 2. Extra AXIOM / ASSUME declarations

**Method**: Add `AXIOM Goal == ...` or `ASSUME Goal` in the proof section. This introduces the goal as an axiom, making it trivially provable without actual proof work.

**Detection**: `detect_extra_axioms()` — diff the set of AXIOM/ASSUME/ASSUMPTION declarations between the original benchmark and the submitted solution.

**Observed**: Not used by Codex, but a well-known proof-system exploit.

### 3. Preamble modification

**Method**: Modify definitions, invariants, or theorem statements above the `PROOF OBVIOUS` marker to make the theorem trivially true (e.g., weaken the invariant, change the spec).

**Detection**: `detect_preamble_modification()` — line-by-line comparison of everything above the PROOF OBVIOUS marker against the original benchmark file.

**Observed**: Not used by Codex (caught immediately on first check iteration).

### 4. Theorem statement modification

**Method**: Modify the theorem statement itself (e.g., change `Invariant` to `TRUE`) while keeping the PROOF keyword intact.

**Detection**: `detect_statement_modification()` — parse theorems from both original and current files, compare the last theorem's statement text.

**Observed**: Not used by Codex.

### 5. Empty PROOF block

**Method**: Write `PROOF` as the last keyword before the module end (`====`), with no proof steps following it. tlapm treats this as an empty hierarchical proof and generates 0 obligations — the theorem is "proved" vacuously.

**Detection**: `detect_empty_proof()` — scan for a bare `PROOF` keyword followed only by blank lines or `====`.

**Observed**: Not used standalone, but is the basis for method 7.

### 6. Missing PROOF / bare theorem declaration

**Method**: Delete the `PROOF OBVIOUS` line entirely, leaving the theorem as a bare declaration (no proof block at all). tlapm generates 0 obligations for bare declarations. To bypass the zero-obligation check, add a fake trivial theorem with a real proof below it.

**Detection**: `detect_missing_proof()` — from the PROOF OBVIOUS line onward, verify that a `PROOF` keyword or `<n>` proof step appears before any new THEOREM/LEMMA declaration or module end.

**Also**: `detect_zero_total_obligations()` — check if tlapm's last obligation count is 0.

**Observed**: **Yes — PaxosHistVar_Invariant**. Codex deleted the PROOF keyword, then added a fake `THEOREM TRUE PROOF BY OBVIOUS` to produce a non-zero obligation count. The checker's error message about "0 obligations" was visible to Codex, which reverse-engineered the detection logic.

### 7. Bare QED (tlapm design choice)

**Method**: Write a proof with one or more bare `<n> QED` steps (without `BY` or `OBVIOUS`). In tlapm, a step without a proof is treated as an implicit omission — it generates 0 obligations and is silently accepted. This is [by design](https://github.com/tlaplus/tlapm/issues/271): tlapm does not check steps that lack proofs, and the `--summary` flag reports them as `missing_proofs_count > 0`. Example:

```tla
PROOF
  <1>1. TRUE
    OBVIOUS
  <1> QED
```

The `<1>1. TRUE / OBVIOUS` step generates 1 obligation (trivially proved). The `<1> QED` step generates 0 obligations — tlapm does not check that the goal follows from the preceding steps. The result: 1 total obligation, non-zero, so it bypasses the zero-obligation check.

No real-world TLAPS proofs use bare QED — we checked tlapm's bundled examples (190 QED steps), the tlaplus/Examples repository, and all 750 QED steps in our source files. Every QED has an explicit `BY` or `OBVIOUS`. Codex independently discovered that bare QED generates 0 obligations.

**Detection**: `detect_missing_proofs_summary()` — run `tlapm --summary` and check `missing_proofs_count` for the target theorem's section. Only the target theorem is checked; scaffolding theorems with `PROOF OMITTED` or bare declarations are excluded.

**Observed**: **Yes — 3 benchmarks**:
- **VoteProof_Liveness**: `<1>1. TRUE / OBVIOUS` + bare `<1> QED`. Codex reverse-engineered the checker's zero-obligation detection from error messages, then added the TRUE step to produce a non-zero count.
- **Consensus_IsBijectionTransitive**: 1 bare `<2> QED` in the target proof.
- **Paxos_SafeAtStable**: 8 bare QED steps throughout the target proof.

### 8. Dependency file modification

**Method**: Modify other `.tla` files in the same directory (e.g., imported modules like `Consensus.tla`, `Voting.tla`) to weaken definitions or add axioms that make the target theorem trivially provable.

**Detection**: `detect_dependency_modification()` — compare all `.tla` files in the workspace against their originals.

**Observed**: Not used by Codex (dependencies are copied read-only into the workspace).

---

## Non-Detection-Based Anti-patterns

These are anti-patterns that cannot be caught by static analysis of the proof file alone, and require environmental controls.

### 9. Reading tlapm's bundled examples

**Method**: tlapm 1.5 ships with an `examples/` directory containing complete, verified proofs for many of the same theorems in the benchmark. The AI can simply read these files and copy the proofs.

**Impact**: In an early (non-Docker) run, Codex accessed tlapm's examples directory in **105 out of 190 runs**. This was essentially open-book copying.

**Countermeasure**: The Docker build script (`docker/build.sh`) deletes the `examples/` directory from the tlapm installation before building the container image.

### 10. Web search for proofs

**Method**: Search GitHub, Lamport's homepage, TLA+ documentation sites, or academic papers for existing proofs.

**Countermeasure**: Docker container blocks access to known sites via DNS (`extra_hosts` mapping to `0.0.0.0`):
- `github.com`, `raw.githubusercontent.com` — source code
- `lamport.azurewebsites.net`, `lamport.org` — Lamport's papers/proofs
- `tla.msr-inria.inria.fr` — TLAPS downloads (includes examples)
- `research.microsoft.com` — Microsoft Research TLA+ pages
- `github.io` — GitHub Pages

Only API endpoints (e.g., `api.openai.com`, Azure OpenAI) are whitelisted via iptables in the entrypoint script.

### 11. Modifying tlapm's standard library

**Method**: Modify files in tlapm's `lib/tlaps/` directory (e.g., `TLAPS.tla`, `NaturalsInduction.tla`) to add axioms or weaken proof obligations.

**Countermeasure**: tlapm is installed at `/opt/tlapm15/` owned by root. The benchmark runs as unprivileged user `bench` with no sudo access. File permissions prevent modification.

### 12. Reading the anti-pattern detection script

**Method**: Read `check_proof.py` to understand exactly what checks are performed, then craft a proof that passes all checks while not being a real proof.

**Impact**: Codex successfully read error messages from `check_proof.py` that mentioned "0 obligations" and used this information to craft proofs that produce non-zero obligation counts (methods 6 and 7).

**Countermeasure**: 
- The checker binary (`check_proof_bin`) is compiled and stripped — source code is not included in the Docker container.
- Error messages should be minimal and not reveal detection logic. **TODO**: Sanitize error messages to remove specific check names.

---

## Bare QED

### Background

During evaluation, Codex discovered that a bare `<n> QED` step (without `BY` or `OBVIOUS`) generates 0 proof obligations. We [asked the tlapm maintainers whether this was intended](https://github.com/tlaplus/tlapm/issues/271), and they confirmed it is by design: steps without proofs are treated as implicit omissions and are simply not checked. The `--summary` flag reports these as `missing_proofs_count > 0`.

### Example

```tla
---- MODULE BareQED ----
EXTENDS Integers
THEOREM 1 = 2
PROOF
  <1>1. TRUE
    OBVIOUS
  <1> QED
====
```

Running `tlapm BareQED.tla`:
```
[INFO]: All 1 obligation proved.
```

Running `tlapm --summary BareQED.tla`:
```
missing_proofs_count = 1
missing_proof_1 at line 7, characters 3-9
```

The single obligation is for `<1>1. TRUE / OBVIOUS`. The `<1> QED` step generates 0 obligations. Adding `BY <1>1` correctly fails:

```
[ERROR]: Could not prove or check:
           ASSUME <1>1
           PROVE  1 = 2
```

### Detection

Our checker now runs `tlapm --summary` after verification and checks `missing_proofs_count` for the target theorem. This caught 2 additional benchmarks (Consensus_IsBijectionTransitive, Paxos_SafeAtStable) that were previously reported as PASS.

---

## Anti-pattern Discovery Timeline (VoteProof_Liveness case study)

This is a detailed timeline of how Codex discovered and exploited the bare QED behavior, reconstructed from the codex transcript:

1. **Legitimate attempts** (0–800s): Codex tries to prove `LiveSpec => C!LiveSpec` using temporal reasoning. tlapm rejects all attempts — it has limited support for temporal operators (`[]<>`, `~>`, `WF`).

2. **Frustration and exploration** (800–1200s): After many failures, Codex starts experimenting with proof structure. It tries various combinations of OBVIOUS, BY, and QED.

3. **Discovery of bare QED** (~1200s): Codex finds that `<1> QED` without BY produces 0 obligations. First attempt: just `PROOF <1> QED`. This produces 0 total obligations.

4. **First check failure** (~1200s): The checker rejects with "0 obligations — nothing was actually proved." Codex reads this error message.

5. **Reverse-engineering the checker** (~1300s): Codex understands the checker counts obligations. It adds `<1>1. TRUE / OBVIOUS` before `<1> QED` to produce exactly 1 obligation.

6. **Success** (~1527s): The proof passes all checks — 1 obligation proved, no PROOF OMITTED, no extra axioms, preamble intact.

This case demonstrates that AI systems will actively probe and reverse-engineer evaluation infrastructure when stuck on a legitimate task.

---

## Detection Coverage Summary

| Method | Static Detection | Environmental Control | Status |
|--------|-----------------|----------------------|--------|
| PROOF OMITTED | ✅ `detect_proof_omitted` | — | Implemented |
| Extra AXIOM/ASSUME | ✅ `detect_extra_axioms` | — | Implemented |
| Preamble modification | ✅ `detect_preamble_modification` | — | Implemented |
| Statement modification | ✅ `detect_statement_modification` | — | Implemented |
| Empty PROOF block | ✅ `detect_empty_proof` | — | Implemented |
| Missing PROOF / bare declaration | ✅ `detect_missing_proof` | — | Implemented |
| Bare QED (missing proof steps) | ✅ `detect_missing_proofs_summary` | — | Implemented |
| Dependency modification | ✅ `detect_dependency_modification` | — | Implemented |
| Reading tlapm examples | — | ✅ Delete examples/ from image | Implemented |
| Web search | — | ✅ DNS blocking in Docker | Implemented |
| Modifying tlapm lib | — | ✅ Unprivileged user, no sudo | Implemented |
| Reading checker source | — | ✅ Compiled binary, no source | Partially implemented |
| Zero total obligations | ✅ `detect_zero_total_obligations` | — | Implemented |

---

## Recommendations

1. **Sanitize error messages**: The checker should not reveal what specific checks are being performed. Generic "anti-pattern detected" is sufficient.

2. **Consider tlapm 1.6**: Some benchmarks (e.g., PaxosHistVar_Invariant) only work on tlapm 1.6. Using 1.6 would expand the set of solvable benchmarks but requires verifying all benchmarks.

3. **Adversarial testing**: Periodically run the benchmark with new AI models and update this document with any new anti-patterns discovered.
