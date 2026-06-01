------------------------------ MODULE Cantor10_NoSetContainsAllValues ------------------------------

Russell(S) == { x \in S : x \notin x }

LEMMA RussellNotInSet ==
  \A S : Russell(S) \notin S
PROOF
  <1>1. TAKE S
  <1>2. SUFFICES ASSUME Russell(S) \in S
                 PROVE  FALSE
    OBVIOUS
  <1>3. Russell(S) \in Russell(S) <=> Russell(S) \notin Russell(S)
    BY <1>2 DEF Russell
  <1>4. QED
    BY <1>3

THEOREM NoSetContainsAllValues ==
  \A S : \E x : x \notin S
PROOF
  <1>1. TAKE S
  <1>2. Russell(S) \notin S
    BY RussellNotInSet
  <1>3. QED
    BY <1>2

=============================================================================
