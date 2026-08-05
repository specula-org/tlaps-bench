---- MODULE Sets_CardinalityOneConverse ----
EXTENDS Sets_CardinalityOneConverseDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
