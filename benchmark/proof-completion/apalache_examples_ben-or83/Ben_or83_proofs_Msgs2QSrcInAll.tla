---- MODULE Ben_or83_proofs_Msgs2QSrcInAll ----
EXTENDS Ben_or83_proofs_Msgs2QSrcInAllScaffold
THEOREM Msgs2QSrcInAll ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsQ2(m) => AsQ2(m).src \in ALL
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
