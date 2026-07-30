---- MODULE Allocator_NextTypeInvariant ----
EXTENDS Allocator_NextTypeInvariantScaffold
THEOREM NextTypeInvariant == TypeInvariant /\ Next => TypeInvariant'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
