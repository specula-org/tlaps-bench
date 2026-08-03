----------------------------- MODULE VoteProofModel ------------------------------

EXTENDS Integers, NaturalsInduction, FiniteSets, FiniteSetTheorems, 
        WellFoundedInduction, TLC, TLAPS

CONSTANT Value,     
         Acceptor,  
         Quorum     

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  

=============================================================================
