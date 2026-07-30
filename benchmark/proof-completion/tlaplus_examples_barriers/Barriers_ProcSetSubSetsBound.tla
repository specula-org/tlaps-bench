---- MODULE Barriers_ProcSetSubSetsBound ----
EXTENDS Barriers_ProcSetSubSetsBoundScaffold
LEMMA ProcSetSubSetsBound ==
    /\ IsFiniteSet(ProcsInRdv) /\ Cardinality(ProcsInRdv) \in 0..N
    /\ IsFiniteSet(ProcsInB1) /\ Cardinality(ProcsInB1) \in 0..N
    /\ IsFiniteSet(ProcsInB1)' /\ Cardinality(ProcsInB1)' \in 0..N
    /\ IsFiniteSet(ProcsInB2) /\ Cardinality(ProcsInB2) \in 0..N
    /\ IsFiniteSet(ProcsInB2)' /\ Cardinality(ProcsInB2)' \in 0..N
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
