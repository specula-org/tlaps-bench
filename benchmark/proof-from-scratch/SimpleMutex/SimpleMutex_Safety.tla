----------------------------- MODULE SimpleMutex_Safety -----------------------------
EXTENDS SimpleMutex

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

THEOREM Safety == Spec => []MutualExclusion
PROOF OBVIOUS

=============================================================================
