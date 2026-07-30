---- MODULE Quicksort_MaxIsMax ----
EXTENDS Quicksort_MaxIsMaxScaffold
LEMMA MaxIsMax == 
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x >= y
    PROVE  x = Max(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
