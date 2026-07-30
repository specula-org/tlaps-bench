---- MODULE Quicksort_PermsOfPermsOf ----
EXTENDS Quicksort_PermsOfPermsOfScaffold
LEMMA PermsOfPermsOf ==
    ASSUME NEW T, NEW s \in Seq(T), NEW t \in PermsOf(s), NEW u \in PermsOf(t)
    PROVE  u \in PermsOf(s)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
