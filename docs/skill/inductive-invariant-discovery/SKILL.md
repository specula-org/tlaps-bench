---
name: inductive-invariant-discovery
description: >-
  Discover and strengthen an inductive invariant when a safety property is true
  but not inductive, so the inductive step of a proof will not close. Use when
  you need an `IndInv` and the missing conjuncts are not obvious; the tool
  reports concrete counterexamples to induction that name the exact state and
  action that break induction.
---

# Discovering inductive invariants

A safety property usually fails to prove because it is **true but not
inductive**: it does not imply its own primed version, so the inductive step
will not close until you add the right extra conjuncts (the *strengthening*).
The `endive` tool (at `$ENDIVE_DIR`) searches for that strengthening
automatically and, whenever a candidate is not yet inductive, hands you precise
feedback about why.

## Describe the problem

Create `$ENDIVE_DIR/benchmarks/<name>.config.json` next to `<name>.tla`:

| field | meaning |
|---|---|
| `safety` | the operator you want to make inductive |
| `typeok` | your `TypeOK` operator |
| `preds` | atomic state predicates the search combines into candidate conjuncts |
| `quant_inv` | quantifier prefix prepended to every candidate (e.g. `\A x \in Node : \E q \in Quorums :`) — this is where you encode the invariant's shape |
| `constants` / `model_consts` | a small finite CONSTANT instantiation so TLC can run |

## Run

```bash
cd "$ENDIVE_DIR"
python3 endive.py --spec benchmarks/<name> \
  --ninvs 15000 --niters 3 --nrounds 4 \
  --num_simulate_traces 50000 --simulate_depth 6 --tlc_workers 6
```

Add `--debug --log_file run.log` to record the full feedback.

## The feedback: counterexamples to induction (CTIs)

The tool samples transitions with **random simulation** (not exhaustive model
checking), and whenever the current candidate is not inductive it emits a
**CTI** — a concrete two-state counterexample:

- **State1** — a state satisfying the current candidate, printed as a TLA+
  conjunction `/\ var = val /\ ...`,
- **an action name** — the transition that breaks induction, and
- **State2** — the successor that violates the candidate.

So instead of "obligation unproved" you learn exactly which conjunct is missing:
"from *this* state, *this* action reaches *that* state, which the invariant
forbids." When the search succeeds it prints the candidate inductive invariant:

```
IndAuto ==
  /\ <safety>
  /\ Inv1_..._def
  /\ Inv2_..._def
```

## Turn the result into a proof

1. Define `IndInv == <safety> /\ <the discovered conjuncts>` above the target.
2. Prove `Init => IndInv`, `IndInv /\ Next => IndInv'` (split per action), and
   `IndInv => <safety>` with tlapm.
3. The discovered conjuncts are hints, not axioms — every lemma you add must be
   fully proved.

## Caveats

- The result is simulation-derived: treat it as a strong hint to verify, not
  ground truth. A candidate can still be missing a conjunct on too small a model.
- If the search stalls, add more semantic `preds`.
- A CTI shows a candidate is not *inductive*; it does not mean the safety
  property itself is false.
