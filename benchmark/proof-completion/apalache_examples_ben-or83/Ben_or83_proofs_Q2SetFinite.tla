---- MODULE Ben_or83_proofs_Q2SetFinite ----
EXTENDS Ben_or83_proofs_Q2SetFiniteScaffold
THEOREM Q2SetFinite ==
  ASSUME TypeOK, NEW r \in ROUNDS
  PROVE  IsFiniteSet(QSet(r)) /\ Cardinality(QSet(r)) <= N
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
