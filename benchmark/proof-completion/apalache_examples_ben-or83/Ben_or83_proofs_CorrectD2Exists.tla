---- MODULE Ben_or83_proofs_CorrectD2Exists ----
EXTENDS Ben_or83_proofs_CorrectD2ExistsScaffold
THEOREM CorrectD2Exists ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1
  PROVE  \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
