---- MODULE Ben_or83_proofs_Msgs2PrimeShape ----
EXTENDS Ben_or83_proofs_Msgs2PrimeShapeScaffold
THEOREM Msgs2PrimeShape ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).r = rr
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
