---- MODULE Sets_CardinalityOneConverse ----
EXTENDS Sets_CardinalityOneConverseScaffold
THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
