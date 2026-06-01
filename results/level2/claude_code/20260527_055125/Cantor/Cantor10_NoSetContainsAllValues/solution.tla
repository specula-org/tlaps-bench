------------------------------ MODULE Cantor10_NoSetContainsAllValues ------------------------------

THEOREM NoSetContainsAllValues ==
  \A S : \E x : x \notin S
PROOF
  <1> TAKE S
  <1> DEFINE R == {y \in S : y \notin y}
  <1>1. R \notin S
    <2>1. R \in R <=> (R \in S /\ R \notin R)
      BY DEF R
    <2>2. QED
      BY <2>1
  <1>2. QED
    BY <1>1

=============================================================================
