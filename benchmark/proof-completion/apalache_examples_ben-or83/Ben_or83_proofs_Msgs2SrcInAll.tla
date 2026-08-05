---- MODULE Ben_or83_proofs_Msgs2SrcInAll ----
EXTENDS Ben_or83_proofs_Msgs2SrcInAllScaffold
THEOREM Msgs2SrcInAll ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).src \in ALL
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
