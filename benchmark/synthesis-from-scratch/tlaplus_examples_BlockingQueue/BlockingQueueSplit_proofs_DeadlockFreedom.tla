--------------------- MODULE BlockingQueueSplit_proofs_DeadlockFreedom ----------------------
EXTENDS BlockingQueueSplit, TLAPS

-----------------------------------------------------------------------------

THEOREM DeadlockFreedom == Spec => []A!Invariant
PROOF OBVIOUS

=============================================================================
