------------------------------- MODULE Voting_ShowsSafety -------------------------------
EXTENDS FiniteSets, TLAPS, Integers
-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
  PROOF OMITTED

Ballot == Nat
-----------------------------------------------------------------------------
VARIABLES votes, maxBal

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
-----------------------------------------------------------------------------
VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b \* have promised
  /\ \E c \in -1..(b-1) :
      /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
-----------------------------------------------------------------------------
Init == 
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b] \* make promise
  /\ UNCHANGED votes

VoteFor(a, b, v) ==
    /\ maxBal[a] <= b \* keep promise
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v) \* safe to vote
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}] \* vote
    /\ maxBal' = [maxBal EXCEPT ![a] = b] \* make promise
-----------------------------------------------------------------------------
Next == 
    \E a \in Acceptor, b \in Ballot : 
        \/ IncreaseMaxBal(a, b)
        \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>
-----------------------------------------------------------------------------
ChosenAt(b, v) == 
    \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Consistency == chosen = {} \/ \E v \in Value : chosen = {v} \* Cardinality(chosen) <= 1
---------------------------------------------------------------------------
CannotVoteAt(a, b) == 
    /\ maxBal[a] > b
    /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) == 
    \E Q \in Quorum : 
        \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == 
    \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

VotesSafe == 
    \A a \in Acceptor, b \in Ballot, v \in Value : 
        VotedFor(a, b, v) => SafeAt(b, v)

OneVote == 
    \A a \in Acceptor, b \in Ballot, v, w \in Value : 
        VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
        VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot
-----------------------------------------------------------------------------
THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)
  PROOF OMITTED

THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value :
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
  PROOF OMITTED

THEOREM OneVoteThm == OneValuePerBallot => OneVote
  PROOF OMITTED

-----------------------------------------------------------------------------
THEOREM VotesSafeImpliesConsistency ==
   ASSUME VotesSafe, OneVote, chosen # {}
   PROVE  \E v \in Value : chosen = {v}
  PROOF OMITTED

THEOREM ShowsSafety ==
          TypeOK /\ VotesSafe /\ OneValuePerBallot =>
             \A Q \in Quorum, b \in Ballot, v \in Value :
               ShowsSafeAt(Q, b, v) => SafeAt(b, v)
PROOF
<1>1. SUFFICES ASSUME TypeOK /\ VotesSafe /\ OneValuePerBallot,
                      NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
                      ShowsSafeAt(Q, b, v)
               PROVE  SafeAt(b, v)
  OBVIOUS
<1>2. PICK c \in -1..(b-1) :
         /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
         /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
  BY <1>1 DEF ShowsSafeAt
<1>3. SUFFICES ASSUME NEW d \in 0..(b-1)
              PROVE  NoneOtherChoosableAt(d, v)
  BY DEF SafeAt
<1>4. d \in Ballot BY <1>1, <1>3, SMT DEF Ballot
<1>5. CASE d < c
  <2>1. c # -1 BY <1>3, <1>5, SMT
  <2>2. PICK a \in Q : VotedFor(a, c, v) BY <1>2, <2>1
  <2>3. c \in Ballot BY <1>2, <2>1, SMT DEF Ballot
  <2>4. a \in Acceptor BY QuorumAssumption, <1>1, <2>2
  <2>5. SafeAt(c, v) BY <1>1, <2>2, <2>3, <2>4 DEF VotesSafe
  <2>6. d \in 0..(c-1) BY <1>3, <1>5, SMT
  <2>. QED BY <2>5, <2>6 DEF SafeAt
<1>6. CASE d = c
  <2>1. c # -1 BY <1>3, <1>6, SMT
  <2>2. PICK a0 \in Q : VotedFor(a0, c, v) BY <1>2, <2>1
  <2>3. \A a \in Q : VotedFor(a, d, v) \/ CannotVoteAt(a, d)
    <3>1. SUFFICES ASSUME NEW a \in Q
                  PROVE  VotedFor(a, d, v) \/ CannotVoteAt(a, d)
      OBVIOUS
    <3>2. d \in Ballot BY <1>4
    <3>3. a \in Acceptor BY QuorumAssumption, <1>1, <3>1
    <3>4. a0 \in Acceptor BY QuorumAssumption, <1>1, <2>2
    <3>5. maxBal[a] >= b BY <1>1, <3>1 DEF ShowsSafeAt
    <3>6. maxBal[a] \in Ballot \cup {-1} BY <1>1, <3>3 DEF TypeOK
    <3>7. maxBal[a] > d BY <1>3, <3>5, <3>6, SMT DEF Ballot
    <3>8. CASE VotedFor(a, d, v) BY <3>8
    <3>9. CASE ~ VotedFor(a, d, v)
      <4>1. DidNotVoteAt(a, d)
        <5>1. SUFFICES ASSUME NEW w \in Value
                      PROVE  ~ VotedFor(a, d, w)
          BY DEF DidNotVoteAt
        <5>2. CASE VotedFor(a, d, w)
          <6>1. w = v BY <1>1, <1>6, <2>2, <3>1, <3>2, <3>3, <3>4, <5>1, <5>2
            DEF OneValuePerBallot
          <6>. QED BY <3>9, <5>2, <6>1
        <5>. QED BY <5>2
      <4>2. CannotVoteAt(a, d) BY <3>7, <4>1 DEF CannotVoteAt
      <4>. QED BY <4>2
    <3>. QED BY <3>8, <3>9
  <2>. QED BY <1>1, <2>3 DEF NoneOtherChoosableAt
<1>7. CASE d > c
  <2>1. d \in (c+1)..(b-1) BY <1>3, <1>7, SMT
  <2>2. \A a \in Q : VotedFor(a, d, v) \/ CannotVoteAt(a, d)
    <3>1. SUFFICES ASSUME NEW a \in Q
                  PROVE  VotedFor(a, d, v) \/ CannotVoteAt(a, d)
      OBVIOUS
    <3>2. a \in Acceptor BY QuorumAssumption, <1>1, <3>1
    <3>3. maxBal[a] >= b BY <1>1, <3>1 DEF ShowsSafeAt
    <3>4. maxBal[a] \in Ballot \cup {-1} BY <1>1, <3>2 DEF TypeOK
    <3>5. maxBal[a] > d BY <1>3, <1>7, <3>3, <3>4, SMT DEF Ballot
    <3>6. DidNotVoteAt(a, d) BY <1>2, <2>1, <3>1
    <3>7. CannotVoteAt(a, d) BY <3>5, <3>6 DEF CannotVoteAt
    <3>. QED BY <3>7
  <2>. QED BY <1>1, <2>2 DEF NoneOtherChoosableAt
<1>8. NoneOtherChoosableAt(d, v) BY <1>3, <1>5, <1>6, <1>7, SMT
<1>. QED BY <1>8

=============================================================================
