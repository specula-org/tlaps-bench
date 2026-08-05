---- MODULE Ben_or83_proofs_Msgs2PrimeQSrcInAll ----
EXTENDS Ben_or83_proofs_Msgs2PrimeQSrcInAllScaffold
THEOREM Msgs2PrimeQSrcInAll ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsQ2(m) => AsQ2(m).src \in ALL
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
