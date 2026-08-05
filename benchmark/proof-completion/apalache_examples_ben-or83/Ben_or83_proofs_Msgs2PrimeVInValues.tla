---- MODULE Ben_or83_proofs_Msgs2PrimeVInValues ----
EXTENDS Ben_or83_proofs_Msgs2PrimeVInValuesScaffold
THEOREM Msgs2PrimeVInValues ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).v \in VALUES
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
