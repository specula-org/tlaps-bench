---- MODULE Ben_or83_proofs_Msgs2Finite ----
EXTENDS Ben_or83_proofs_Msgs2FiniteScaffold
THEOREM Msgs2Finite ==
  ASSUME TypeOK, NEW r \in ROUNDS
  PROVE  IsFiniteSet(msgs2[r])
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
