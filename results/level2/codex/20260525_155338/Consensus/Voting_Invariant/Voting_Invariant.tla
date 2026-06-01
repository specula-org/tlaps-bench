------------------------------- MODULE Voting_Invariant -------------------------------
EXTENDS FiniteSets, TLAPS, Integers
-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat
-----------------------------------------------------------------------------
VARIABLES votes, maxBal

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
-----------------------------------------------------------------------------
VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b 
  /\ \E c \in -1..(b-1) :
      /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
-----------------------------------------------------------------------------
Init == 
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b] 
  /\ UNCHANGED votes

VoteFor(a, b, v) ==
    /\ maxBal[a] <= b 
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v) 
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}] 
    /\ maxBal' = [maxBal EXCEPT ![a] = b] 
-----------------------------------------------------------------------------
Next == 
    \E a \in Acceptor, b \in Ballot : 
        \/ IncreaseMaxBal(a, b)
        \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>
-----------------------------------------------------------------------------

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

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
        VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

Vars == <<votes, maxBal>>

LEMMA InitInv == Init => Inv
PROOF
  BY SMT DEF Init, Inv, TypeOK, VotesSafe, OneValuePerBallot,
             SafeAt, NoneOtherChoosableAt, VotedFor, Ballot

LEMMA StutterInv == Inv /\ UNCHANGED Vars => Inv'
PROOF
  BY SMT DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, SafeAt,
             NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt,
             VotedFor, Vars

LEMMA TypeOKNext == TypeOK /\ Next => TypeOK'
PROOF
  BY SMT DEF TypeOK, Next, IncreaseMaxBal, VoteFor, Ballot

LEMMA OneValuePerBallotNext ==
  TypeOK /\ OneValuePerBallot /\ Next => OneValuePerBallot'
PROOF
  BY SMT DEF TypeOK, OneValuePerBallot, Next, IncreaseMaxBal,
             VoteFor, VotedFor, Ballot

LEMMA ShowsSafety ==
  TypeOK /\ VotesSafe /\ OneValuePerBallot =>
    \A Q \in Quorum, b \in Ballot, v \in Value :
      ShowsSafeAt(Q, b, v) => SafeAt(b, v)
PROOF
  <1>1. SUFFICES ASSUME TypeOK,
                         VotesSafe,
                         OneValuePerBallot,
                         NEW Q \in Quorum,
                         NEW b \in Ballot,
                         NEW v \in Value,
                         ShowsSafeAt(Q, b, v)
                  PROVE  SafeAt(b, v)
    BY SMT
  <1>2. PICK c \in -1..(b-1) :
            /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
            /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
    BY <1>1 DEF ShowsSafeAt
  <1>3. \A a \in Q : maxBal[a] >= b
    BY <1>1 DEF ShowsSafeAt
  <1>4. \A r \in 0..(b-1) : NoneOtherChoosableAt(r, v)
  PROOF
    <2>1. SUFFICES ASSUME NEW r \in 0..(b-1)
                    PROVE  NoneOtherChoosableAt(r, v)
      BY SMT
    <2>2. CASE r < c
    PROOF
      <3>1. c # -1 /\ \E a \in Q : VotedFor(a, c, v)
        BY <1>2, <2>1, <2>2, SMT
      <3>2. PICK a0 \in Q : VotedFor(a0, c, v)
        BY <3>1
      <3>3. a0 \in Acceptor
        BY <1>1, <3>2, QuorumAssumption DEF QuorumAssumption
      <3>4. c \in Ballot
        BY <1>2, <2>1, <2>2, SMT DEF Ballot
      <3>5. SafeAt(c, v)
        BY <1>1, <3>2, <3>3, <3>4 DEF VotesSafe
      <3>6. r \in 0..(c-1)
        BY <2>1, <2>2, SMT
      <3>7. QED
        BY <3>5, <3>6 DEF SafeAt
    <2>3. CASE r = c
    PROOF
      <3>1. c # -1 /\ \E a \in Q : VotedFor(a, c, v)
        BY <1>2, <2>1, <2>3, SMT
      <3>2. PICK a0 \in Q : VotedFor(a0, c, v)
        BY <3>1
      <3>3. c \in Ballot
        BY <1>2, <2>1, <2>3, SMT DEF Ballot
      <3>4. a0 \in Acceptor
        BY <1>1, <3>2, QuorumAssumption DEF QuorumAssumption
      <3>5. \A a \in Q : VotedFor(a, c, v) \/ CannotVoteAt(a, c)
      PROOF
        <4>1. SUFFICES ASSUME NEW a \in Q
                        PROVE  VotedFor(a, c, v) \/ CannotVoteAt(a, c)
          BY SMT
        <4>2. CASE VotedFor(a, c, v)
          BY <4>2
        <4>3. CASE ~VotedFor(a, c, v)
        PROOF
          <5>1. a \in Acceptor
            BY <1>1, <4>1, QuorumAssumption DEF QuorumAssumption
          <5>2. maxBal[a] >= b
            BY <1>3, <4>1
          <5>3. b > c
            BY <2>1, <2>3, SMT DEF Ballot
          <5>4. maxBal[a] \in Int
            BY <1>1, <5>1, SMT DEF TypeOK, Ballot
          <5>5. b \in Int /\ c \in Int
            BY <1>1, <3>3, SMT DEF Ballot
          <5>6. maxBal[a] > c
            BY <5>2, <5>3, <5>4, <5>5, SimpleArithmetic
          <5>7. DidNotVoteAt(a, c)
          PROOF
            <6>1. SUFFICES ASSUME NEW w \in Value,
                                   VotedFor(a, c, w)
                            PROVE  FALSE
              BY SMT DEF DidNotVoteAt
            <6>2. w = v
              BY <1>1, <3>2, <3>3, <3>4, <5>1, <6>1
                 DEF OneValuePerBallot
            <6>3. QED
              BY <4>3, <6>1, <6>2
          <5>8. QED
            BY <5>6, <5>7 DEF CannotVoteAt
        <4>4. QED
          BY <4>2, <4>3
      <3>6. \A a \in Q : VotedFor(a, r, v) \/ CannotVoteAt(a, r)
        BY <2>3, <3>5, SMT
      <3>7. QED
        BY <1>1, <3>6 DEF NoneOtherChoosableAt
    <2>4. CASE r > c
    PROOF
      <3>1. \A a \in Q : CannotVoteAt(a, r)
      PROOF
        <4>1. SUFFICES ASSUME NEW a \in Q
                        PROVE  CannotVoteAt(a, r)
          BY SMT
        <4>2. a \in Acceptor
          BY <1>1, <4>1, QuorumAssumption DEF QuorumAssumption
        <4>3. maxBal[a] >= b
          BY <1>3, <4>1
        <4>4. b > r
          BY <2>1, SMT DEF Ballot
        <4>5. maxBal[a] \in Int
          BY <1>1, <4>2, SMT DEF TypeOK, Ballot
        <4>6. b \in Int /\ r \in Int
          BY <1>1, <2>1, SMT DEF Ballot
        <4>7. maxBal[a] > r
          BY <4>3, <4>4, <4>5, <4>6, SimpleArithmetic
        <4>8. r \in (c+1)..(b-1)
          BY <2>1, <2>4, SMT
        <4>9. DidNotVoteAt(a, r)
          BY <1>2, <4>1, <4>8
        <4>10. QED
          BY <4>7, <4>9 DEF CannotVoteAt
      <3>2. QED
        BY <1>1, <3>1 DEF NoneOtherChoosableAt
    <2>5. QED
      BY <2>2, <2>3, <2>4, SMT
  <1>5. QED
    BY <1>4 DEF SafeAt

LEMMA NoneOtherStableIncrease ==
  ASSUME Inv,
         NEW a \in Acceptor,
         NEW b \in Ballot,
         IncreaseMaxBal(a, b)
  PROVE  \A c \in Ballot, v \in Value :
           NoneOtherChoosableAt(c, v) => NoneOtherChoosableAt(c, v)'
PROOF
  <1>1. SUFFICES ASSUME NEW c \in Ballot,
                         NEW v \in Value,
                         NoneOtherChoosableAt(c, v)
                  PROVE  NoneOtherChoosableAt(c, v)'
    BY SMT
  <1>2. PICK QQ \in Quorum :
            \A x \in QQ : VotedFor(x, c, v) \/ CannotVoteAt(x, c)
    BY <1>1 DEF NoneOtherChoosableAt
  <1>3. \A x \in QQ : VotedFor(x, c, v)' \/ CannotVoteAt(x, c)'
  PROOF
    <2>1. SUFFICES ASSUME NEW x \in QQ
                    PROVE  VotedFor(x, c, v)' \/ CannotVoteAt(x, c)'
      BY SMT
    <2>2. CASE VotedFor(x, c, v)
    PROOF
      <3>1. VotedFor(x, c, v)'
        BY <1>1, <2>2 DEF IncreaseMaxBal, VotedFor
      <3>2. QED
        BY <3>1
    <2>3. CASE CannotVoteAt(x, c)
    PROOF
      <3>1. DidNotVoteAt(x, c)'
        BY <1>1, <2>3 DEF IncreaseMaxBal, CannotVoteAt,
                           DidNotVoteAt, VotedFor
      <3>2. maxBal'[x] > c
      PROOF
        <4>1. CASE x = a
        PROOF
          <5>1. maxBal'[x] = b
            BY <1>1, <4>1, SMT DEF Inv, TypeOK, IncreaseMaxBal, Ballot
          <5>2. b > c
            BY <1>1, <2>3, <4>1, SMT
               DEF Inv, TypeOK, IncreaseMaxBal, CannotVoteAt, Ballot
          <5>3. QED
            BY <5>1, <5>2
        <4>2. CASE x # a
        PROOF
          <5>1. maxBal'[x] = maxBal[x]
            BY <1>1, <1>2, <2>1, <4>2, QuorumAssumption, SMT
               DEF Inv, TypeOK, IncreaseMaxBal, QuorumAssumption, Ballot
          <5>2. maxBal[x] > c
            BY <2>3 DEF CannotVoteAt
          <5>3. QED
            BY <5>1, <5>2
        <4>3. QED
          BY <4>1, <4>2, SMT
      <3>3. CannotVoteAt(x, c)'
        BY <3>1, <3>2 DEF CannotVoteAt
      <3>4. QED
        BY <3>3
    <2>4. QED
      BY <1>2, <2>1, <2>2, <2>3, SMT
  <1>4. QED
    BY <1>1, <1>3 DEF NoneOtherChoosableAt

LEMMA NoneOtherStableVote ==
  ASSUME Inv,
         NEW a \in Acceptor,
         NEW b \in Ballot,
         NEW v \in Value,
         VoteFor(a, b, v)
  PROVE  \A c \in Ballot, w \in Value :
           NoneOtherChoosableAt(c, w) => NoneOtherChoosableAt(c, w)'
PROOF
  BY SMTT(60), QuorumAssumption
     DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, VoteFor,
         ShowsSafeAt, SafeAt, NoneOtherChoosableAt, CannotVoteAt,
         DidNotVoteAt, VotedFor, Ballot, QuorumAssumption

LEMMA SafeAtStable ==
  Inv /\ Next /\ TypeOK' =>
    \A b \in Ballot, v \in Value :
      SafeAt(b, v) => SafeAt(b, v)'
PROOF
  BY SMTT(60), NoneOtherStableIncrease, NoneOtherStableVote
     DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, Next,
         IncreaseMaxBal, VoteFor, ShowsSafeAt, SafeAt,
         NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt,
         VotedFor, Ballot

LEMMA VotesSafeNext == Inv /\ Next /\ TypeOK' => VotesSafe'
PROOF
  BY SMT, ShowsSafety, SafeAtStable
     DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, Next,
         IncreaseMaxBal, VoteFor, ShowsSafeAt, SafeAt,
         NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt,
         VotedFor, Ballot

LEMMA NextInv == Inv /\ Next => Inv'
PROOF
  BY SMT, TypeOKNext, OneValuePerBallotNext, VotesSafeNext
     DEF Inv

LEMMA InvInductive == Inv /\ [Next]_Vars => Inv'
PROOF
  BY SMT, NextInv, StutterInv DEF Vars

-----------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
PROOF
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_Vars => Inv'
    BY InvInductive
  <1>3. Spec => []Inv
    BY <1>1, <1>2, PTL DEF Spec, Vars
  <1>4. QED
    BY <1>3 DEF Vars
----------------------------------------------------------------------------
----------------------------------------------------------------------------

=============================================================================
