---- MODULE Quicksort_IntervalMinMax ----
EXTENDS Quicksort_IntervalMinMaxScaffold
LEMMA IntervalMinMax ==
    ASSUME NEW i \in Int, NEW j \in Int, i <= j
    PROVE  i = Min(i .. j) /\ j = Max(i .. j)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
