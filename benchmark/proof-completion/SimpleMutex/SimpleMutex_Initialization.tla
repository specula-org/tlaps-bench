---- MODULE SimpleMutex_Initialization ----
EXTENDS SimpleMutex_InitializationScaffold
THEOREM Initialization == Init => TypeOK /\ Inv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
