---- MODULE Allocator_InitTypeInvariant ----
EXTENDS Allocator_InitTypeInvariantScaffold
THEOREM InitTypeInvariant == Init => TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
