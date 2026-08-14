------------------------------- MODULE tcp ----------------------------------

EXTENDS Integers, Sequences, SequencesExt, FiniteSets

CONSTANT 
    Peers

ASSUME PeersAssumption == Cardinality(Peers) = 2

VARIABLE
    tcb,
    connstate,
    network

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

Inv ==

    \A local, remote \in { p \in Peers : network[p] = <<>> } :
        connstate[local] = "ESTABLISHED" <=> connstate[remote] = "ESTABLISHED"

=============================================================================
