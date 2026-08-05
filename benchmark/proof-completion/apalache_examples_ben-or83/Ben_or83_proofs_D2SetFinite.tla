---- MODULE Ben_or83_proofs_D2SetFinite ----
EXTENDS Ben_or83_proofs_D2SetFiniteScaffold
THEOREM D2SetFinite ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  IsFiniteSet(DvSet(r, v)) /\ Cardinality(DvSet(r, v)) <= N
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
