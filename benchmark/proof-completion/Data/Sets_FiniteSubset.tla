---- MODULE Sets_FiniteSubset ----
EXTENDS Sets_FiniteSubsetScaffold
THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
