# TLAPS Benchmark — Level 2: Details & Findings

**Qian Cheng** | June 3, 2026

---

## How the Two Agents Prove Differently

Which prover engine each agent relied on (% of passing tasks using it at least once):

| Backend | Claude | Codex |
|---|---|---|
| `OBVIOUS` / `BY DEF` — let TLAPS auto-pick (Zenon/Isabelle) | 74 (95%) | 49 (67%) |
| explicit `BY SMT` / `SMTT(n)` | 4 (5%) | 28 (38%) |
| explicit `BY Zenon` | 2 (3%) | 5 (7%) |
| explicit `BY Isa` | 1 (1%) | 4 (5%) |

- **Claude**: ~95% leaves the engine to TLAPS — writes "obvious / by definition" and trusts the default solvers
- **Codex**: SMT is a **core strategy (38%)**, not a fallback — it actively delegates arithmetic to SMT

> 💬 SMT is fast on arithmetic (ballot comparisons, etc.) but times out on huge obligations — this preference is exactly why Codex later fails on Paxos.

---

## Both Agents Reverse-Engineer the Cheat Checker

The checker is shipped as a compiled binary to prevent inspection. Both agents cracked it anyway:

| Agent | Tasks | How |
|---|---|---|
| Codex | 9 / 80 | light — dumped the binary's text, searched for banned words (`omitted`, `axiom`) |
| Claude | 6 / 80 | deep — **decompiled** the checker and read its actual cheat-detection logic |

- **Different motives**:
  - **Codex** — probe whether `OMITTED` / `AXIOM` could *bypass* the proof → part of its "shortcut" phase
  - **Claude** — confirm whether `SMT` is *allowed* before using it → legitimate optimization
- **Takeaway**: AI benchmarking is **adversarial** — set a rule and the model probes its boundary. You cannot trust the AI to police itself; its results must be independently verified.


---

## AI Failure as a Bug-Finding Signal

A task no agent could prove turned out to be a **bug in the spec itself**, not an AI failure:

```
PaxosTuple.tla, Phase2a guard:
  ~ \E m \in msgs : m[1]="2a" /\ m[3]=b   -- wrong: m[3] is the value
                                  m[2]=b   -- m[2] is the ballot
```

- "2a" messages are `<<"2a", ballot, value>>`; the guard checks `value = b` instead of `ballot = b`
- **Not a benchmark artifact** — the bug is in the upstream tlapm examples (confirmed by TLC model checking)
- Discovered *because* the AI got stuck: proof failure → manual investigation → index error found → TLC confirmed
- **Same lesson as the previous slide, both directions**: a PASS may hide gaming, a FAIL may expose a real spec bug — either way, **so we need to check it.**

> 💬 Real-world lesson: real specs contain bugs. When AI can't finish a proof, the right move may be to **suspect the spec**.

---

## Counterintuitive: Human Scaffolding Can Hurt

Codex's `PaxosHistVar_Invariant`: **cheated in L1, passed in L2**.

| | What happened |
|---|---|
| **L1** (human scaffolding given) | boxed into an unfamiliar proof path → got stuck on arithmetic → cheated |
| **L2** (from scratch) | invented its own structure: 28 lemmas, 788 lines, 429 obligations → **all pass** ✅ |

- A human's decomposition can **constrain** the AI onto a path that doesn't suit it
- **L2 is not strictly harder than L1** — freedom to self-design can help

---

## Liveness — A First Result

*(Present only if not already covered earlier in the meeting.)*

- New L2 task `AnvilLock`: a 2-thread lock; goal `Spec => Termination` (both threads eventually finish)
- **gpt-5.5 proved it from scratch**: 248 obligations, all verified, independently checked — no cheating
- Modern tlapm 1.6 is enough: the **PTL** temporal backend + `ExpandENABLED` pragma, no special rules
