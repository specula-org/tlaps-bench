---- MODULE Ben_or83_proofs_QFaultyMono ----
EXTENDS Ben_or83_proofs_QFaultyMonoScaffold
THEOREM QFaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(QPSet(r))
          /\ Cardinality(QSet(r)) <= Cardinality(QPSet(r))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
