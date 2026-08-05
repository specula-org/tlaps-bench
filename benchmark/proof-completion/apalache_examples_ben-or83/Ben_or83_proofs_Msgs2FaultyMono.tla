---- MODULE Ben_or83_proofs_Msgs2FaultyMono ----
EXTENDS Ben_or83_proofs_Msgs2FaultyMonoScaffold
THEOREM Msgs2FaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(msgs2'[r])
          /\ Cardinality(msgs2[r]) <= Cardinality(msgs2'[r])
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
