---- MODULE Quicksort_AutomorphismsCompose ----
EXTENDS Quicksort_AutomorphismsComposeScaffold
LEMMA AutomorphismsCompose ==
    ASSUME NEW S, NEW f \in Automorphisms(S), NEW g \in Automorphisms(S)
    PROVE  f ** g \in Automorphisms(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
