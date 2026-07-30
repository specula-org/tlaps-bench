---- MODULE SimpleMutex_Mutex ----
EXTENDS SimpleMutex_MutexScaffold
THEOREM Mutex == Inv => MutualExclusion
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
