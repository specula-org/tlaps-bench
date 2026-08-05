---- MODULE Ben_or83_proofs_Msgs2SenderPartitionBound ----
EXTENDS Ben_or83_proofs_Msgs2SenderPartitionBoundScaffold
THEOREM Msgs2SenderPartitionBound ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW S, S \subseteq msgs2[r]
  PROVE  Cardinality(Senders2(S))
           <= Cardinality(DPart(S, 0)) + Cardinality(DPart(S, 1)) + Cardinality(QPart(S))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
