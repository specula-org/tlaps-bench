---- MODULE Ben_or83_proofs_Msgs1Shape ----
EXTENDS Ben_or83_proofs_Msgs1ShapeScaffold
THEOREM Msgs1Shape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs1[rr] : m.r = rr /\ m.src \in ALL
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
