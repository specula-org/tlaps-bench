---- MODULE Ben_or83_proofs_SupportedSingletonPinsNextM1 ----
EXTENDS Ben_or83_proofs_SupportedSingletonPinsNextM1Scaffold
THEOREM SupportedSingletonPinsNextM1 ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW m \in msgs1[r + 1],
         m.src \in CORRECT
  PROVE  m.v = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
