---- MODULE Ben_or83_proofs_Pres_L1_S3_DecidedCarry ----
EXTENDS Ben_or83_proofs_Pres_L1_S3_DecidedCarryScaffold
THEOREM Pres_L1_S3_DecidedCarry ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0),
         decision' = decision, decision[id0] # NO_DECISION
  PROVE  /\ Cardinality(msgs2'[round[id0]]) >= N - T
         /\ Cardinality({ m \in msgs2'[round[id0]]: IsD2(m) /\ AsD2(m).v = decision[id0] }) >= T + 1
         /\ 2 * Cardinality({ m \in msgs2'[round[id0]]: IsD2(m) /\ AsD2(m).v = decision[id0] }) > N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
