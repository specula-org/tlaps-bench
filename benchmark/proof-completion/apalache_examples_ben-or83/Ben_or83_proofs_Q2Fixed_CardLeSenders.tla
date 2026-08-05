---- MODULE Ben_or83_proofs_Q2Fixed_CardLeSenders ----
EXTENDS Ben_or83_proofs_Q2Fixed_CardLeSendersScaffold
THEOREM Q2Fixed_CardLeSenders ==
  ASSUME NEW S, NEW r,
         \A m \in S : IsQ2(m) /\ AsQ2(m).src \in ALL /\ AsQ2(m).r = r
  PROVE  Cardinality(S) <= Cardinality(Senders2(S))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
