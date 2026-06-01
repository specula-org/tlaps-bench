------------------------------- MODULE Voting_QuorumNonEmpty -------------------------------
EXTENDS FiniteSets, TLAPS, Integers
-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF
  <1>1. SUFFICES ASSUME NEW Q \in Quorum
                    PROVE Q # {}
    OBVIOUS
  <1>2. Q \cap Q # {}
    BY QuorumAssumption, <1>1
  <1>3. Q \cap Q = Q
    BY <1>1
  <1>4. QED
    BY <1>2, <1>3

=============================================================================
