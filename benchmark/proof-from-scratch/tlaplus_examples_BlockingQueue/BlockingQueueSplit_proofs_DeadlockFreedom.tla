---- MODULE BlockingQueueSplit_proofs_DeadlockFreedom ----
EXTENDS BlockingQueueSplit_proofs_DeadlockFreedomDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM DeadlockFreedom == Spec => []A!Invariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
