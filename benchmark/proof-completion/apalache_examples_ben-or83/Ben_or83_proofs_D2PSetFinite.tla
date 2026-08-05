---- MODULE Ben_or83_proofs_D2PSetFinite ----
EXTENDS Ben_or83_proofs_D2PSetFiniteScaffold
THEOREM D2PSetFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  IsFiniteSet(DvPSet(r, v)) /\ Cardinality(DvPSet(r, v)) <= N
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
