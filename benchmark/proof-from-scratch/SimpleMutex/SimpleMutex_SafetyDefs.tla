----------------------------- MODULE SimpleMutex_SafetyDefs -----------------------------
EXTENDS SimpleMutexModel

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

=============================================================================
