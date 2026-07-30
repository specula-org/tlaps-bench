---- MODULE Cantor10_NoSetContainsAllValues ----
EXTENDS Cantor10_NoSetContainsAllValuesScaffold
THEOREM NoSetContainsAllValues ==
  \A S : \E x : x \notin S
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
