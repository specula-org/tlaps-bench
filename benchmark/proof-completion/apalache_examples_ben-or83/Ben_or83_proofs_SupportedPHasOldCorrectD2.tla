---- MODULE Ben_or83_proofs_SupportedPHasOldCorrectD2 ----
EXTENDS Ben_or83_proofs_SupportedPHasOldCorrectD2Scaffold
THEOREM SupportedPHasOldCorrectD2 ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS, NEW v \in SupportedValuesP(r)
  PROVE  \E m \in msgs2[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
