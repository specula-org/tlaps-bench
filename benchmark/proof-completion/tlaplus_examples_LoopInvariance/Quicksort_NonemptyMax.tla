---- MODULE Quicksort_NonemptyMax ----
EXTENDS Quicksort_NonemptyMaxScaffold
LEMMA NonemptyMax ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S
    PROVE  /\ Max(S) \in S
           /\ x <= Max(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
