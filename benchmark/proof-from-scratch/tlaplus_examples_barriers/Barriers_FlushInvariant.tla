---- MODULE Barriers_FlushInvariant ----
EXTENDS Barriers_FlushInvariantDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM FlushInvariant == Spec => []FlushInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
