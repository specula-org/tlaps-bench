---- MODULE Ben_or83_proofs_QPSetFinite ----
EXTENDS Ben_or83_proofs_QPSetFiniteScaffold
THEOREM QPSetFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS
  PROVE  IsFiniteSet(QPSet(r)) /\ Cardinality(QPSet(r)) <= N
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
