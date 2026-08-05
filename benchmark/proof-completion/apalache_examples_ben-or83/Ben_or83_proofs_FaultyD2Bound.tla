---- MODULE Ben_or83_proofs_FaultyD2Bound ----
EXTENDS Ben_or83_proofs_FaultyD2BoundScaffold
THEOREM FaultyD2Bound ==
  ASSUME NEW r, NEW v,
         \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r
  PROVE  Cardinality(FaultyD2(r, v)) <= F
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
