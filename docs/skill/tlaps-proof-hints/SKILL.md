---
name: tlaps-proof-hints
description: >-
  Non-obvious TLAPS gotchas that block an otherwise valid proof and that provers
  and strong models do not resolve on their own. Use when a TLA+ proof will not
  close for no clear reason — in particular when a `BY I!Foo` citation of a
  theorem or fact from an instantiated module (`I == INSTANCE M`) silently fails
  and the instantiated module `M` has `ASSUME` declarations.
---

# TLAPS proving hints

Sharp edges that make `tlapm` reject an otherwise valid proof and that capable
provers do not discover on their own.

## Using a theorem from an instantiated module (`BY I!Thm`)

When you create an instance `I == INSTANCE M`, all assumptions of `M` become
additional hypotheses of every theorem instance. So `I!Thm` does not stand for
the bare fact `M` proved — it carries the instantiated assumptions as
hypotheses, which you must discharge.

The trap is when an assumption mentions an operator imported through `EXTENDS`
(here `Pos`, from a common module `Lib`). The instance re-exports it under the
`I!` prefix (`I!Pos`), while the importer keeps the unprefixed name (`Pos`).
These are the same operator but two distinct internal symbols, and the back-ends
do not relate them automatically: `I!Thm` carries `I!Pos(N)` while the local
assumption `NA` only establishes `Pos(N)`, so even `BY I!Thm, NA` is not enough.
The remedy is a **bridge** theorem equating the prefixed operator with its local
counterpart, cited alongside the instantiated theorem:

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
