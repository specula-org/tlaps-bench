------------------------------- MODULE Paxos_NoneNotAValueScaffold -------------------------------
(* 
Specification and Verification of Basic Paxos.

See http://research.microsoft.com/en-us/um/people/lamport/pubs/pubs.html#paxos-simple
*)
EXTENDS PaxosModel_2

LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
PROOF OMITTED

=============================================================================
