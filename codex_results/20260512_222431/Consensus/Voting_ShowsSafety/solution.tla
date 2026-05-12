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
<1>1. SUFFICES ASSUME TypeOK, VotesSafe, OneValuePerBallot,
                    NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
                    ShowsSafeAt(Q, b, v)
             PROVE  SafeAt(b, v)
  OBVIOUS
<1>2. \A a \in Q : a \in Acceptor
  BY <1>1, QuorumAssumption
<1>3. PICK c \in -1..(b-1) :
        /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
        /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
  BY <1>1 DEF ShowsSafeAt
<1>4. \A d \in 0..(b-1) : NoneOtherChoosableAt(d, v)
  <2>1. SUFFICES ASSUME NEW d \in 0..(b-1)
                 PROVE  NoneOtherChoosableAt(d, v)
    OBVIOUS
  <2>2. CASE d < c
    <3>1. c # -1
      BY <1>3, <2>1, <2>2, SMT DEF Ballot
    <3>2. PICK a \in Q : VotedFor(a, c, v)
      BY <1>3, <3>1
    <3>3. a \in Acceptor
      BY <1>2, <3>2
    <3>4. c \in Ballot
      BY <1>3, <2>1, <2>2, SMT DEF Ballot
    <3>5. SafeAt(c, v)
      BY <1>1, <3>2, <3>3, <3>4 DEF VotesSafe
    <3>6. d \in 0..(c-1)
      BY <2>1, <2>2, SMT
    <3> QED
      BY <3>5, <3>6 DEF SafeAt
  <2>3. CASE d = c
    <3>1. c # -1
      BY <2>1, <2>3, SMT DEF Ballot
    <3>2. PICK a0 \in Q : VotedFor(a0, c, v)
      BY <1>3, <3>1
    <3>3. a0 \in Acceptor
      BY <1>2, <3>2
    <3>4. d \in Ballot
      BY <2>1, SMT DEF Ballot
    <3>5. \A a \in Q : VotedFor(a, d, v) \/ CannotVoteAt(a, d)
      <4>1. SUFFICES ASSUME NEW a \in Q
                     PROVE  VotedFor(a, d, v) \/ CannotVoteAt(a, d)
        OBVIOUS
      <4>2. VotedFor(a, d, v) \/ ~ VotedFor(a, d, v)
        OBVIOUS
      <4>3. ASSUME VotedFor(a, d, v)
             PROVE  VotedFor(a, d, v) \/ CannotVoteAt(a, d)
        BY <4>3
      <4>4. ASSUME ~ VotedFor(a, d, v)
             PROVE  VotedFor(a, d, v) \/ CannotVoteAt(a, d)
        <5>1. a \in Acceptor
          BY <1>2, <4>1
        <5>2. maxBal[a] >= b
          BY <1>1, <4>1 DEF ShowsSafeAt
        <5>3. b > d
          BY <1>1, <2>1, SMT DEF Ballot
        <5>4. maxBal[a] \in Ballot \cup {-1}
          BY <1>1, <5>1 DEF TypeOK
        <5>5. maxBal[a] > d
          BY <5>2, <5>3, <5>4, SMT DEF Ballot
        <5>6. DidNotVoteAt(a, d)
          <6>1. SUFFICES ASSUME NEW w \in Value
                         PROVE  ~ VotedFor(a, d, w)
            BY DEF DidNotVoteAt
          <6>2. ASSUME VotedFor(a, d, w)
                 PROVE  FALSE
            <7>1. VotedFor(a0, d, v)
              BY <2>3, <3>2
            <7>2. w = v
              BY <1>1, <3>3, <3>4, <5>1, <6>1, <6>2, <7>1 DEF OneValuePerBallot
            <7>3. VotedFor(a, d, v)
              BY <6>2, <7>2
            <7> QED
              BY <4>4, <7>3
          <6> QED
            BY <6>1, <6>2
        <5> QED
          BY <5>5, <5>6 DEF CannotVoteAt
      <4>5. VotedFor(a, d, v) => VotedFor(a, d, v) \/ CannotVoteAt(a, d)
        BY <4>3
      <4>6. (~ VotedFor(a, d, v)) => VotedFor(a, d, v) \/ CannotVoteAt(a, d)
        BY <4>4
      <4> QED
        BY <4>2, <4>5, <4>6
    <3> QED
      BY <3>5 DEF NoneOtherChoosableAt
  <2>4. CASE d > c
    <3>1. d \in (c+1)..(b-1)
      BY <2>1, <2>4, SMT
    <3>2. \A a \in Q : CannotVoteAt(a, d)
      <4>1. SUFFICES ASSUME NEW a \in Q
                     PROVE  CannotVoteAt(a, d)
        OBVIOUS
      <4>2. maxBal[a] >= b
        BY <1>1, <4>1 DEF ShowsSafeAt
      <4>3. b > d
        BY <1>1, <3>1, SMT DEF Ballot
      <4>4. a \in Acceptor
        BY <1>2, <4>1
      <4>5. maxBal[a] \in Ballot \cup {-1}
        BY <1>1, <4>4 DEF TypeOK
      <4>6. maxBal[a] > d
        BY <4>2, <4>3, <4>5, SMT DEF Ballot
      <4>7. DidNotVoteAt(a, d)
        BY <1>3, <3>1, <4>1
      <4> QED
        BY <4>6, <4>7 DEF CannotVoteAt
    <3> QED
      BY <3>2 DEF NoneOtherChoosableAt
  <2> QED
    BY <2>2, <2>3, <2>4
<1> QED
  BY <1>4 DEF SafeAt


=============================================================================
