---- MODULE Quicksort_MinIsMin ----
EXTENDS Quicksort_MinIsMinScaffold
LEMMA MinIsMin == 
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x <= y
    PROVE  x = Min(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
