---- MODULE Allocator_NextTypeInvariant ----
EXTENDS Allocator_NextTypeInvariantDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM NextTypeInvariant == TypeInvariant /\ Next => TypeInvariant'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
