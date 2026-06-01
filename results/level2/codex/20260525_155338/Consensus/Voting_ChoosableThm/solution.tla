------------------------------- MODULE Voting_ChoosableThm -------------------------------
EXTENDS FiniteSets, TLAPS, Integers
-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat
-----------------------------------------------------------------------------
VARIABLES votes, maxBal

-----------------------------------------------------------------------------
VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
ChosenAt(b, v) == 
    \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

---------------------------------------------------------------------------
CannotVoteAt(a, b) == 
    /\ maxBal[a] > b
    /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) == 
    \E Q \in Quorum : 
        \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

-----------------------------------------------------------------------------

THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value :
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
PROOF
  <1>1. TAKE b \in Ballot, v \in Value
  <1>2. ASSUME ChosenAt(b, v)
        PROVE  NoneOtherChoosableAt(b, v)
    PROOF
      <2>1. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
        BY <1>2 DEF ChosenAt
      <2>2. \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
        BY <2>1
      <2>3. Q \in Quorum
        BY <2>1
      <2> QED
        BY <2>2, <2>3 DEF NoneOtherChoosableAt
  <1> QED
    BY <1>2

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
----------------------------------------------------------------------------
----------------------------------------------------------------------------

=============================================================================
