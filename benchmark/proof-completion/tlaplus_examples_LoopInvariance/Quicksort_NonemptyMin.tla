---- MODULE Quicksort_NonemptyMin ----
EXTENDS Quicksort_NonemptyMinScaffold
LEMMA NonemptyMin ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S
    PROVE  /\ Min(S) \in S 
           /\ Min(S) <= x
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
