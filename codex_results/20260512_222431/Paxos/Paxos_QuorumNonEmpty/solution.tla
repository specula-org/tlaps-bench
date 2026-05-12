------------------------------- MODULE Paxos_QuorumNonEmpty -------------------------------
(* 
Specification and Verification of Basic Paxos.

See http://research.microsoft.com/en-us/um/people/lamport/pubs/pubs.html#paxos-simple
*)
EXTENDS Integers, TLAPS, TLC
-----------------------------------------------------------------------------
CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}                 

LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
PROOF
  <1>1. Quorums \subseteq SUBSET Acceptors
    BY QuorumAssumption
  <1>2. \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
    BY QuorumAssumption
  <1>3. \A Q \in Quorums : Q # {}
  PROOF
    <2>1. TAKE Q \in Quorums
    <2>2. Q \cap Q # {}
      BY <1>2, <2>1
    <2>3. Q # {}
      BY <2>2
    <2>4. QED
      BY <2>3
  <1>4. QED
    BY <1>3

=============================================================================
