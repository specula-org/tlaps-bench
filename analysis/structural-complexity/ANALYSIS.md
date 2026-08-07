# Structural complexity for Proof Completion

We looked at every task in the current proof-completion manifest
(`benchmark/proof-completion/manifest.json`, 706 tasks) and asked a simple
question: which structural properties of the *human* reference proof actually
tell us something about difficulty?

The four candidates were:

1. **Reference proof steps** — how many explicit `<n>` step lines the human
   proof has. A proof that is just `BY ...` has no numbered steps; we call
   that **Direct**, not “zero.”
2. **Max proof depth** — deepest `<n>` level. Same number of steps can be a
   flat list or a tall tree.
3. **Transitive proof dependencies** — how many user-defined definitions and
   previously proved theorems you eventually touch if you follow the facts and
   `DEF`s cited in the reference proof.
4. **Reference proof obligations** — how many leaf obligations `tlapm` generates
   when that reference proof is ported into the layered task.

Supporting files: `metrics.csv` / `metrics.json` (per task), `summary.json`
(aggregates), `scripts/structural_complexity_pc.py` (to recompute).

## How we measured them

For each task we recovered the original proof from `source/` the same way
`validate` does. Steps and depth are plain text counts on that proof. Deps start
from names cited in `BY` / `USE` / `DEF`, then close over SANY’s operator graph
plus each cited lemma’s own citations, restricted to the source module and its
local `EXTENDS` / `INSTANCE` neighbors (stdlib and backends like Z3 are out).
Obligations come from `tlapm --summary` after porting the proof into the
benchmark task (scaffold lemmas stay `PROOF OMITTED`).

## Coverage

705 of 706 tasks have a measurable reference proof. The one miss is
`OpenAddressing/OpenAddressing_proof_CompleteSafety.tla`: the theorem exists in
`source/OpenAddressing/OpenAddressing_proof.tla`, but its body is already
`PROOF OBVIOUS`, so there is no human hierarchical/`BY` proof to score. For the
other 705, all four metrics are present; SANY and `tlapm --summary` both
completed cleanly.

About 215 proofs are Direct; 490 are structured. Where Composer 2.5 already
recorded `gt_proof_steps`, our step counts match on 408 / 441 tasks. The
mismatches are mostly old Cantor entries whose stored Composer value doesn’t
line up with the current source text — our count follows the TLAPS file as it
is now.

Composer pass-rate trends below use the 449 overlapping tasks that have a
verdict. The suite has grown since that run (apalache Ben-or / Tendermint are
mostly missing from it), so treat those trends as supportive, not definitive.

## What the suite looks like

Most proofs are small. Among structured ones the median is 10 steps; three
quarters are at most 22. There is a long tail: 19 tasks have 101+ steps, and
the extreme is `tcp_proof_IndInvSystem` at 1433.

Rough step bands:

| Band | Tasks |
|------|------:|
| Direct | 215 |
| 1–4 | 127 |
| 5–12 | 167 |
| 13–30 | 116 |
| 31–50 | 38 |
| 51–100 | 23 |
| 101+ | 19 |

Depth is usually shallow. Of the structured proofs, 208 top out at `<1>`,
another 128 at `<2>`. Only 45 go to depth 5 or more; the maximum we saw is 9
(`AtomicBakery` inductive invariant and a large EWD998 proof).

Dependencies are more spread out: median 9, but the top end is 263 — and that
maximum is a *Direct* proof (`Ben_or83_proofs_Inductive`), which is already a
hint that deps are not just “another size measure.”

Obligations track size closely. Median 11, max 2780 (again the TCP inductive
proof). On structured proofs you typically get a bit over two obligations per
step.

## Spot checks

We re-checked a handful of tasks by hand.

`GCD_GCD2` is the clean Direct case: `BY DEF GCD`, zero steps, depth 0, one
obligation, and four transitive defs (`GCD` pulls in `SetMax`, `DivisorsOf`,
`Divides`). `GCD_GCD3` is the small structured cousin — three `<1>` steps, still
those four defs, three obligations.

Cantor shows the other extreme of deps: `Cantor3` has 16 steps and depth 5, but
cites no lemmas or defs, so deps stay 0. The difficulty is the nesting, not the
library. (Our citation scrape sometimes picks junk like `x` / `in` out of a
formula; those names don’t survive the “must be a user-defined op or theorem”
filter, so the closure stays honest.)

Ben-or’s `Inductive` is the important Direct counterexample. The proof is a
single `BY` of a dozen preservation lemmas plus `DEF IndInv`. Steps say
“trivial”; deps say 263. If the leaderboard only showed step count, this would
look easy for the wrong reason.

On the obligation side, Allocator is useful: `AllocateTypeInvariant` is Direct
with one obligation, while `AllocateMutex` has 25 steps and 79 obligations but
only four deps — same neighborhood of the spec, very different prover load.
The TCP inductive proofs sit at the far end (1433 steps / 2780 obligations) and
Composer fails them.

## Do the newer metrics add anything?

This was the real question. Steps and depth we already roughly understand;
deps and obligations are only worth keeping if they aren’t just restating size.

On the 490 structured proofs, Spearman correlation is:

- steps vs obligations: **0.97**
- steps vs depth: **0.86**
- steps vs deps: **0.34**
- depth vs deps: **0.23**

So obligations almost rank tasks the same way steps do. Depth moves with steps
too, though not quite as tightly. Dependencies are the odd one out — weakly
tied to size, which is what you want from a complementary signal.

You can see that inside a single steps band. For proofs with 5–12 steps, deps
still range from 0 to 156; obligations barely move. Even at a fixed step count
of exactly 10, we saw depths 1–3 and deps from 1 all the way to 156.

Composer’s pass rates fall as each metric grows, but once you hold steps fixed,
deps still separate passes from fails (e.g. in the 13–30 band, fails average
~15 deps vs ~9 for passes; in 31+, ~27 vs ~17). Obligations barely budge inside
those bands except in the huge tail. That matches the correlation story:
obligations mostly tag along with steps; deps carry leftover difficulty.

## Takeaway

For the public leaderboard, **reference proof steps** (with an explicit
**Direct** band) is still the right primary axis. It’s easy to explain, already
what the website uses, and it tracks model success cleanly. Don’t put
obligations next to it as a second complexity score — reviewers would
essentially be looking at the same ranking twice.

Keep the other three as metadata, mainly for Core selection:

- **Deps** are the useful complement. They catch “short proof, heavy prior
  reasoning” tasks that steps alone mis-rank. When we cut a Core set, we should
  deliberately keep some Direct+high-deps and some structured+low-deps cells,
  not only long proofs.
- **Depth** is a lighter shape signal. Handy when you want both flat and nested
  proofs at similar size; too coarse and too correlated with steps to lead the
  leaderboard on its own.
- **Obligations** are still worth recording for timeouts and prover cost. They
  just shouldn’t drive the difficulty label.

Suggested public bands (same spirit as the current site): Direct, 1–4, 5–12,
13–30, 31–50, 51–100, 101+.

## Caveats

Deps combine a text scrape of citations with SANY. That’s good enough for this
pass, but odd operator names (`**`, `p1`, …) and formula tokens in `BY` clauses
are messy around the edges. We also scope each task to its source module
closure on purpose — merging a whole example directory by bare name earlier
inflated Euclid-style counts.

Obligations are measured on the layered PC task after porting, which is what
the agent actually faces, not a dump of the entire original multi-theorem file.

Composer trends cover only part of today’s suite. Before freezing Core cuts,
worth rechecking against a full-suite run.

## Recompute

```bash
uv run python scripts/structural_complexity_pc.py
uv run python scripts/structural_complexity_pc.py --skip-obligations
uv run python scripts/structural_complexity_pc.py --examples Euclid,Cantor --limit 20
```
