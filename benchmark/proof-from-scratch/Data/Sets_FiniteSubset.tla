---- MODULE Sets_FiniteSubset ----
EXTENDS Sets_FiniteSubsetDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
