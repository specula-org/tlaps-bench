------------------------------- MODULE Voting_QuorumNonEmptyDefs -------------------------------

EXTENDS Integers, TLAPS
CONSTANT Value,     
         Acceptor,  
         Quorum     

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  

=============================================================================

