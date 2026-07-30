---- MODULE Quicksort_PartitionsLemma ----
EXTENDS Quicksort_PartitionsLemmaScaffold
LEMMA PartitionsLemma ==
    ASSUME NEW T, NEW s \in Seq(T), NEW I \in SUBSET (1 .. Len(s)),
           NEW p \in I, NEW t \in Partitions(I, p, s)
    PROVE  /\ t \in Seq(T)
           /\ Len(t) = Len(s)
           /\ \A i \in (1 .. Len(s)) \ I : t[i] = s[i]
           /\ \A i \in I : \E j \in I : t[i] = s[j]
           /\ \A i,j \in I : i <= p /\ p < j => t[i] <= t[j]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
