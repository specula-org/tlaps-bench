---- MODULE Ben_or83_proofs_Msgs2PrimeSrcInAll ----
EXTENDS Ben_or83_proofs_Msgs2PrimeSrcInAllScaffold
THEOREM Msgs2PrimeSrcInAll ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).src \in ALL
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
