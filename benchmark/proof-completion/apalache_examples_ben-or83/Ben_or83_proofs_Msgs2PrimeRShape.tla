---- MODULE Ben_or83_proofs_Msgs2PrimeRShape ----
EXTENDS Ben_or83_proofs_Msgs2PrimeRShapeScaffold
THEOREM Msgs2PrimeRShape ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
