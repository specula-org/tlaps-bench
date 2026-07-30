---- MODULE tcp_proof_TypeOKInductive ----
EXTENDS tcp_proof_TypeOKInductiveScaffold
LEMMA TypeOKInductive == TypeOK /\ [Next]_vars => TypeOK'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
