---- MODULE Sets_IntervalCardinality ----
EXTENDS Sets_IntervalCardinalityDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM IntervalCardinality ==  
  ASSUME NEW a \in Nat, NEW b \in Nat 
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
