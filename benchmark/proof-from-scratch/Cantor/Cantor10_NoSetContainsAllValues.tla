---- MODULE Cantor10_NoSetContainsAllValues ----
EXTENDS Cantor10_NoSetContainsAllValuesDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM NoSetContainsAllValues ==
  \A S : \E x : x \notin S
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
