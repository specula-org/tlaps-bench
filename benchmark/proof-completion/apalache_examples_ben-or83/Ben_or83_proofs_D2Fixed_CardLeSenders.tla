---- MODULE Ben_or83_proofs_D2Fixed_CardLeSenders ----
EXTENDS Ben_or83_proofs_D2Fixed_CardLeSendersScaffold
THEOREM D2Fixed_CardLeSenders ==
  ASSUME NEW S, NEW r, NEW v,
         \A m \in S : IsD2(m) /\ AsD2(m).src \in ALL
                       /\ AsD2(m).r = r /\ AsD2(m).v = v
  PROVE  Cardinality(S) <= Cardinality(Senders2(S))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
