---
name: tlaps-proof-hints
description: Resolve TLAPS proof failures involving theorem instances from modules with assumptions. Use when a citation such as BY I!Thm does not close a goal because prefixed and unprefixed imported operators are treated as different symbols.
---

# Use a theorem from an instantiated module

## Symptom

A citation such as `BY I!Thm, NA` does not close the goal even though `I!Thm` appears to prove it and `NA` appears to supply the corresponding local assumption.

## Cause

When a module with assumptions is instantiated as `I == INSTANCE M`, the instantiated assumptions become hypotheses of its theorem instances. If an assumption mentions an operator imported through `EXTENDS`, the instance re-exports that operator under the `I!` prefix. TLAPS treats the prefixed and unprefixed names as distinct internal symbols, so backends do not automatically relate `I!Pos(N)` to `Pos(N)`.

## Fix

Prove a bridge theorem equating the prefixed operator with its local counterpart and cite it alongside the instantiated theorem:

```tla
---- MODULE Lib ----
EXTENDS Integers
Pos(n) == n > 0
====


---- MODULE A ----
EXTENDS Lib
CONSTANT N
ASSUME NA == Pos(N)

THEOREM Thm == N > 0
  BY NA DEF Pos
====


---- MODULE B ----
EXTENDS Lib
CONSTANT N
ASSUME NA == Pos(N)

I == INSTANCE A

THEOREM Bridge == \A n : I!Pos(n) = Pos(n)
  BY DEF I!Pos, Pos

THEOREM Test == N > 0
\*  BY I!Thm, NA            \* FAILS
  BY I!Thm, NA, Bridge      \* WORKS
====
```

Source: [tlaplus/tlapm#279](https://github.com/tlaplus/tlapm/pull/279)
