---- MODULE Quicksort_PermsOfLemma ----
EXTENDS Quicksort_PermsOfLemmaScaffold
LEMMA PermsOfLemma ==
    ASSUME NEW T, NEW s \in Seq(T), NEW t \in PermsOf(s)
    PROVE  /\ t \in Seq(T)
           /\ Len(t) = Len(s)
           /\ \A i \in 1 .. Len(s) : \E j \in 1 .. Len(s) : t[i] = s[j]
           /\ \A i \in 1 .. Len(s) : \E j \in 1 .. Len(t) : t[j] = s[i]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
