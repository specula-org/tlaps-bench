# TLAPS Benchmark: Experience & Discussion Points

**Ruize Tang** | May 19, 2026

---

## My Exploration: Proof Completion Benchmark

- Stripped proof bodies from a collection of TLAPS specs, keeping THEOREM statements
- Asked AI to fill in proofs ([with one prompt](https://github.com/tangruize/tlaps-bench/blob/63ab0dd7794b0ce92ff0efd439f695a08b316aca/run_codex_benchmark.py#L208)), checked with TLAPS verifier and a cheat checker
- Built automated benchmark: [tangruize/tlaps-bench](https://github.com/tangruize/tlaps-bench)

### Results (Codex GPT-5.5, single run)

| | Count |
|---|---|
| Total theorems | 193 |
| AI verified | 186 (96.4%) |
| AI failed/cheated | 7 (3+4) |
| Human OMITTED | 12 |
| Human failed (version issues) | 8 |

- AI pass rate **exceeds** that of human-written proofs in the same benchmark
- Most remaining failures likely solvable with more prompt iterations
- **Conclusion**: proof completion is approaching saturation for frontier AI

### AI Cheating is Creative

- Documented all observed anti-patterns: [PROOF_ANTIPATTERNS.md](https://github.com/tangruize/tlaps-bench/blob/master/PROOF_ANTIPATTERNS.md)
- Examples: using AXIOM/OMITTED to skip obligations, citing network-fetched proofs, smuggling assumptions in TLAPS libs, exploiting bugs in anti-cheating logic
- In early evaluation without guardrails, AI found answers in TLAPS built-in examples and the internet — only 1 liveness theorem remained unsolved ([old results](https://github.com/tangruize/tlaps-bench/tree/b69a405c717e30745f91893bab19513fe3b43954))
- **Without guardrails, benchmark scores are unreliable**

---

## Observations on PR [#211](https://github.com/tlaplus/Examples/pull/211) and [#212](https://github.com/tlaplus/Examples/pull/212)

- **PR #211**: Safety proofs for 20+ specs **from scratch**
  - No proof scaffolding; AI designs lemma structure and writes all steps
  - More realistic than proof completion
- **PR #212**: Using Apalache as a **counterexample-driven feedback loop** to discover inductive invariants, then TLAPS to mechanically discharge obligations
  - Particularly interesting approach
- **Both PRs**: Newly added proofs focus on safety; liveness obligations left OMITTED

---

## Two Benchmark Levels

Based on my exploration and the PRs above, I see two distinct levels of difficulty for a TLAPS benchmark:

### Level 1: Proof Completion

- Given: THEOREM + proof scaffolding (invariants defined, lemmas decomposed)
- Task: fill proof bodies
- Evaluation metric: pass/fail (verified by TLAPS + cheat checker)
- Status: **frontier AI approaching saturation** (96.4% with GPT-5.5)

### Level 2: Proof from Scratch

- Given: bare TLA+ spec with safety/liveness properties stated
- Task: find inductive invariants, design lemma structure, write proof
- This is what PRs #211 and #212 explore (human-guided, AI-assisted)
- Evaluation metric: pass/fail may not be sufficient — how to measure **partial progress** when some obligations remain OMITTED or failed?
- Difficulty distribution may be uneven (DieHard vs TCP)

---

## Discussion Points

**1. Evaluation Metric for Level 2**

- [tlaplus/Examples](https://github.com/tlaplus/Examples) has plenty of specs for building a benchmark
- For Level 1, pass/fail per theorem is a reasonable starting point (scope is already small)
- For Level 2, when some obligations remain OMITTED or failed, how do we measure partial progress?
- How to ensure the benchmark has good discrimination across difficulty levels?

**2. Liveness**

- Both PR [#211](https://github.com/tlaplus/Examples/pull/211) and [#212](https://github.com/tlaplus/Examples/pull/212) focus on safety; liveness obligations left OMITTED
- Liveness/temporal reasoning is a distinctive strength of TLA+ and an area where AI tends to struggle
- A benchmark covering liveness would have stronger discrimination
- What level of temporal reasoning can TLAPS currently support?
