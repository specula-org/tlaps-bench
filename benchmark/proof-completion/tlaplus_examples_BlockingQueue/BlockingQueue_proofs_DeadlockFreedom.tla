---- MODULE BlockingQueue_proofs_DeadlockFreedom ----
EXTENDS BlockingQueue_proofs_DeadlockFreedomScaffold
THEOREM DeadlockFreedom == Spec => []Invariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
