---- MODULE SimpleMutex_Invariance ----
EXTENDS SimpleMutex_InvarianceScaffold
THEOREM Invariance == TypeOK /\ Inv /\ Next => TypeOK' /\ Inv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
