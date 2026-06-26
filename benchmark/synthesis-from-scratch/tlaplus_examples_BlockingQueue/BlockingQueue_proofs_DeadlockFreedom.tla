------------------------ MODULE BlockingQueue_proofs_DeadlockFreedom ------------------------
EXTENDS BlockingQueue, TLAPS

THEOREM DeadlockFreedom == Spec => []Invariant
PROOF OBVIOUS

=============================================================================
