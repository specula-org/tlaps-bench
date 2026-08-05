---- MODULE Ben_or83_proofs_Msgs2Shape ----
EXTENDS Ben_or83_proofs_Msgs2ShapeScaffold
THEOREM Msgs2Shape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).r = rr
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
