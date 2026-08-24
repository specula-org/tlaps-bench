---- MODULE Allocator_InitTypeInvariant ----
EXTENDS Allocator_InitTypeInvariantDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM InitTypeInvariant == Init => TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
