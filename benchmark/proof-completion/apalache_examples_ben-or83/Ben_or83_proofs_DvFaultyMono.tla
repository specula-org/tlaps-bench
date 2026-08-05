---- MODULE Ben_or83_proofs_DvFaultyMono ----
EXTENDS Ben_or83_proofs_DvFaultyMonoScaffold
THEOREM DvFaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  /\ IsFiniteSet(DvPSet(r, v))
          /\ Cardinality(DvSet(r, v)) <= Cardinality(DvPSet(r, v))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
