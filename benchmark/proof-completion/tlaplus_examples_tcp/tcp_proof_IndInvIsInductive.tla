---- MODULE tcp_proof_IndInvIsInductive ----
EXTENDS tcp_proof_IndInvIsInductiveScaffold
THEOREM IndInvIsInductive == IndInv /\ [Next]_vars => IndInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
