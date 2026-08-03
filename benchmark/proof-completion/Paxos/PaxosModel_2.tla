------------------------------- MODULE PaxosModel_2 -------------------------------

EXTENDS Integers, TLAPS, TLC
CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}                 

Ballots == Nat

None == CHOOSE v : v \notin Values

=============================================================================
