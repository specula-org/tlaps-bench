---- MODULE BinarySearch_SortedLess ----
EXTENDS BinarySearch_SortedLessScaffold
LEMMA SortedLess ==
    ASSUME NEW s \in SortedSeqs, NEW i \in 1 .. Len(s), NEW j \in 1 .. Len(s),
           s[i] < s[j]
    PROVE  i < j
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
