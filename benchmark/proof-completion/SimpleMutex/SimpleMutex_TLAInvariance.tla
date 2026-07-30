---- MODULE SimpleMutex_TLAInvariance ----
EXTENDS SimpleMutex_TLAInvarianceScaffold
THEOREM TLAInvariance == TypeOK /\ Inv /\ [Next]_vars => TypeOK' /\ Inv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
