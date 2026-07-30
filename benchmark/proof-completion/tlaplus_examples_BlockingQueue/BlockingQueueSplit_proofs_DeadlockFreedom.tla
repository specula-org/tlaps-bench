---- MODULE BlockingQueueSplit_proofs_DeadlockFreedom ----
EXTENDS BlockingQueueSplit_proofs_DeadlockFreedomScaffold
THEOREM DeadlockFreedom == Spec => []A!Invariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
