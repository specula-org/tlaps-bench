---- MODULE BlockingQueue_proofs_DeadlockFreedom ----
EXTENDS BlockingQueue_proofs_DeadlockFreedomDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM DeadlockFreedom == Spec => []Invariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
