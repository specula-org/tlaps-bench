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

LEMMA InitInv == Init => Inv
BY DEF Init, Inv, TypeOK, VotesSafe, OneValuePerBallot, VotedFor, Ballot

-----------------------------------------------------------------------------

LEMMA NextTypeOK ==
  ASSUME TypeOK, [Next]_<<votes, maxBal>>
  PROVE  TypeOK'
<1>1. CASE UNCHANGED <<votes, maxBal>>
  BY <1>1 DEF TypeOK
<1>2. ASSUME NEW a \in Acceptor, NEW b \in Ballot, IncreaseMaxBal(a, b)
      PROVE  TypeOK'
  BY <1>2 DEF IncreaseMaxBal, TypeOK, Ballot
<1>3. ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value, VoteFor(a, b, v)
      PROVE  TypeOK'
  <2>1. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    BY <1>3 DEF VoteFor
  <2>2. votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    BY DEF TypeOK
  <2>3. votes[a] \cup {<<b, v>>} \in SUBSET (Ballot \X Value)
    <3>1. votes[a] \subseteq Ballot \X Value
      BY <2>2
    <3>2. <<b, v>> \in Ballot \X Value
      OBVIOUS
    <3> QED BY <3>1, <3>2
  <2>4. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]
    BY <2>1, <2>2, <2>3
  <2>5. maxBal' \in [Acceptor -> Ballot \cup {-1}]
    BY <1>3 DEF VoteFor, TypeOK, Ballot
  <2> QED BY <2>4, <2>5 DEF TypeOK
<1> QED BY <1>1, <1>2, <1>3 DEF Next

-----------------------------------------------------------------------------

LEMMA SafeAtStable ==
  ASSUME TypeOK, [Next]_<<votes, maxBal>>,
         NEW bb \in Ballot, NEW vv \in Value, SafeAt(bb, vv)
  PROVE  SafeAt(bb, vv)'
<1> SUFFICES ASSUME NEW c \in 0..(bb-1)
             PROVE  NoneOtherChoosableAt(c, vv)'
  BY DEF SafeAt
<1>1. NoneOtherChoosableAt(c, vv)
  BY DEF SafeAt
<1>2. PICK Q \in Quorum : \A a \in Q : VotedFor(a, c, vv) \/ CannotVoteAt(a, c)
  BY <1>1 DEF NoneOtherChoosableAt
<1>3. SUFFICES \A a \in Q : VotedFor(a, c, vv)' \/ CannotVoteAt(a, c)'
  BY DEF NoneOtherChoosableAt
<1> TAKE a \in Q
<1>4. a \in Acceptor
  BY QuorumAssumption
<1>5. VotedFor(a, c, vv) \/ CannotVoteAt(a, c)
  BY <1>2
<1>6. CASE UNCHANGED <<votes, maxBal>>
  <2>1. votes' = votes
    BY <1>6
  <2>2. maxBal' = maxBal
    BY <1>6
  <2>3. CASE VotedFor(a, c, vv)
    BY <2>1, <2>3 DEF VotedFor
  <2>4. CASE CannotVoteAt(a, c)
    <3>1. maxBal[a] > c
      BY <2>4 DEF CannotVoteAt
    <3>2. DidNotVoteAt(a, c)
      BY <2>4 DEF CannotVoteAt
    <3>3. \A w \in Value : <<c, w>> \notin votes'[a]
      <4> TAKE w \in Value
      <4>1. ~ VotedFor(a, c, w)
        BY <3>2 DEF DidNotVoteAt
      <4>2. <<c, w>> \notin votes[a]
        BY <4>1 DEF VotedFor
      <4> QED BY <4>2, <2>1
    <3>4. DidNotVoteAt(a, c)'
      BY <3>3 DEF DidNotVoteAt, VotedFor
    <3>5. maxBal'[a] > c
      BY <3>1, <2>2
    <3> QED BY <3>4, <3>5 DEF CannotVoteAt
  <2> QED BY <1>5, <2>3, <2>4
<1>7. ASSUME NEW a1 \in Acceptor, NEW b1 \in Ballot, IncreaseMaxBal(a1, b1)
      PROVE  VotedFor(a, c, vv)' \/ CannotVoteAt(a, c)'
  <2>1. votes' = votes
    BY <1>7 DEF IncreaseMaxBal
  <2>2. CASE VotedFor(a, c, vv)
    BY <2>1, <2>2 DEF VotedFor
  <2>3. CASE CannotVoteAt(a, c)
    <3>1. maxBal[a] > c
      BY <2>3 DEF CannotVoteAt
    <3>2. DidNotVoteAt(a, c)
      BY <2>3 DEF CannotVoteAt
    <3>3. \A w \in Value : <<c, w>> \notin votes'[a]
      <4> TAKE w \in Value
      <4>1. ~ VotedFor(a, c, w)
        BY <3>2 DEF DidNotVoteAt
      <4>2. <<c, w>> \notin votes[a]
        BY <4>1 DEF VotedFor
      <4> QED BY <4>2, <2>1
    <3>4. DidNotVoteAt(a, c)'
      BY <3>3 DEF DidNotVoteAt, VotedFor
    <3>5. maxBal'[a] > c
      <4>1. CASE a = a1
        <5>1. maxBal'[a1] = b1
          BY <1>7 DEF IncreaseMaxBal, TypeOK
        <5>2. b1 > maxBal[a1]
          BY <1>7 DEF IncreaseMaxBal
        <5>3. maxBal[a1] > c
          BY <3>1, <4>1
        <5>4. maxBal[a1] \in Ballot \cup {-1}
          BY <4>1, <1>4 DEF TypeOK
        <5> QED BY <5>1, <5>2, <5>3, <5>4, <4>1 DEF Ballot
      <4>2. CASE a # a1
        <5>1. maxBal' = [maxBal EXCEPT ![a1] = b1]
          BY <1>7 DEF IncreaseMaxBal
        <5>2. maxBal'[a] = maxBal[a]
          BY <5>1, <4>2, <1>4 DEF TypeOK
        <5> QED BY <5>2, <3>1
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>4, <3>5 DEF CannotVoteAt
  <2> QED BY <1>5, <2>2, <2>3
<1>8. ASSUME NEW a1 \in Acceptor, NEW b1 \in Ballot, NEW v1 \in Value, VoteFor(a1, b1, v1)
      PROVE  VotedFor(a, c, vv)' \/ CannotVoteAt(a, c)'
  <2>1. votes' = [votes EXCEPT ![a1] = votes[a1] \cup {<<b1, v1>>}]
    BY <1>8 DEF VoteFor
  <2>2. maxBal' = [maxBal EXCEPT ![a1] = b1]
    BY <1>8 DEF VoteFor
  <2>3. votes'[a] = IF a = a1 THEN votes[a1] \cup {<<b1, v1>>} ELSE votes[a]
    BY <2>1, <1>4 DEF TypeOK
  <2>4. maxBal'[a] = IF a = a1 THEN b1 ELSE maxBal[a]
    BY <2>2, <1>4 DEF TypeOK
  <2>5. CASE VotedFor(a, c, vv)
    <3>1. <<c, vv>> \in votes[a]
      BY <2>5 DEF VotedFor
    <3>2. <<c, vv>> \in votes'[a]
      BY <2>3, <3>1
    <3> QED BY <3>2 DEF VotedFor
  <2>6. CASE CannotVoteAt(a, c)
    <3>1. maxBal[a] > c
      BY <2>6 DEF CannotVoteAt
    <3>2. DidNotVoteAt(a, c)
      BY <2>6 DEF CannotVoteAt
    <3>3. CASE a = a1
      <4>1. maxBal[a] <= b1
        BY <1>8, <3>3 DEF VoteFor
      <4>0. maxBal[a] \in Ballot \cup {-1}
        BY <1>4 DEF TypeOK
      <4>2. b1 > c
        BY <4>1, <3>1, <4>0 DEF Ballot
      <4>3. b1 # c
        BY <4>2
      <4>4. votes'[a] = votes[a] \cup {<<b1, v1>>}
        BY <2>3, <3>3
      <4>5. \A w \in Value : <<c, w>> \notin votes'[a]
        <5> TAKE w \in Value
        <5>1. ~ VotedFor(a, c, w)
          BY <3>2 DEF DidNotVoteAt
        <5>2. <<c, w>> \notin votes[a]
          BY <5>1 DEF VotedFor
        <5>3. <<c, w>> # <<b1, v1>>
          BY <4>3
        <5> QED BY <4>4, <5>2, <5>3
      <4>5a. DidNotVoteAt(a, c)'
        BY <4>5 DEF DidNotVoteAt, VotedFor
      <4>6. maxBal'[a] = b1
        BY <2>4, <3>3
      <4>7. maxBal'[a] > c
        BY <4>2, <4>6
      <4> QED BY <4>5a, <4>7 DEF CannotVoteAt
    <3>4. CASE a # a1
      <4>1. votes'[a] = votes[a]
        BY <2>3, <3>4
      <4>2. maxBal'[a] = maxBal[a]
        BY <2>4, <3>4
      <4>3. \A w \in Value : <<c, w>> \notin votes'[a]
        <5> TAKE w \in Value
        <5>1. ~ VotedFor(a, c, w)
          BY <3>2 DEF DidNotVoteAt
        <5>2. <<c, w>> \notin votes[a]
          BY <5>1 DEF VotedFor
        <5> QED BY <4>1, <5>2
      <4>3a. DidNotVoteAt(a, c)'
        BY <4>3 DEF DidNotVoteAt, VotedFor
      <4>4. maxBal'[a] > c
        BY <3>1, <4>2
      <4> QED BY <4>3a, <4>4 DEF CannotVoteAt
    <3> QED BY <3>3, <3>4
  <2> QED BY <1>5, <2>5, <2>6
<1> QED BY <1>6, <1>7, <1>8 DEF Next

-----------------------------------------------------------------------------

LEMMA ShowsSafetyLemma ==
  ASSUME Inv, NEW Q \in Quorum, NEW bb \in Ballot, NEW vv \in Value,
         ShowsSafeAt(Q, bb, vv)
  PROVE  SafeAt(bb, vv)
<1> SUFFICES ASSUME NEW c0 \in 0..(bb-1)
             PROVE  NoneOtherChoosableAt(c0, vv)
  BY DEF SafeAt
<1>1. PICK c \in -1..(bb-1) :
        /\ (c # -1) => \E a \in Q : VotedFor(a, c, vv)
        /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteAt(a, d)
  BY DEF ShowsSafeAt
<1>2. \A a \in Q : maxBal[a] \geq bb
  BY DEF ShowsSafeAt
<1>3. CASE c < c0
  <2>1. c0 \in (c+1)..(bb-1)
    BY <1>3
  <2>2. \A a \in Q : DidNotVoteAt(a, c0)
    BY <2>1, <1>1
  <2>3. \A a \in Q : CannotVoteAt(a, c0)
    <3> TAKE a \in Q
    <3>1. a \in Acceptor
      BY QuorumAssumption
    <3>1a. maxBal[a] \in Ballot \cup {-1}
      BY <3>1 DEF Inv, TypeOK
    <3>2. maxBal[a] \geq bb
      BY <1>2
    <3>3. maxBal[a] > c0
      BY <3>2, <2>1, <3>1a DEF Ballot
    <3>4. DidNotVoteAt(a, c0)
      BY <2>2
    <3> QED BY <3>3, <3>4 DEF CannotVoteAt
  <2> QED BY <2>3 DEF NoneOtherChoosableAt
<1>4. CASE c0 = c
  <2>1. c \in 0..(bb-1)
    BY <1>4
  <2>2. c # -1
    BY <2>1
  <2>3. PICK a2 \in Q : VotedFor(a2, c, vv)
    BY <1>1, <2>2
  <2>4. a2 \in Acceptor
    BY QuorumAssumption
  <2>5. c \in Ballot
    BY <2>1 DEF Ballot
  <2>6. \A a \in Q : VotedFor(a, c, vv) \/ CannotVoteAt(a, c)
    <3> TAKE a \in Q
    <3>1. a \in Acceptor
      BY QuorumAssumption
    <3>2. CASE VotedFor(a, c, vv)
      BY <3>2
    <3>3. CASE ~ VotedFor(a, c, vv)
      <4>1. \A w \in Value : ~ VotedFor(a, c, w)
        <5> TAKE w \in Value
        <5>1. CASE w = vv
          BY <3>3, <5>1
        <5>2. CASE w # vv
          <6> SUFFICES ASSUME VotedFor(a, c, w) PROVE FALSE
            OBVIOUS
          <6>1. vv = w
            BY <2>3, <2>4, <3>1, <2>5 DEF Inv, OneValuePerBallot
          <6> QED BY <6>1, <5>2
        <5> QED BY <5>1, <5>2
      <4>2. DidNotVoteAt(a, c)
        BY <4>1 DEF DidNotVoteAt
      <4>3. maxBal[a] \geq bb
        BY <1>2
      <4>3a. maxBal[a] \in Ballot \cup {-1}
        BY <3>1 DEF Inv, TypeOK
      <4>4. maxBal[a] > c
        BY <4>3, <2>1, <4>3a DEF Ballot
      <4>5. CannotVoteAt(a, c)
        BY <4>2, <4>4 DEF CannotVoteAt
      <4> QED BY <4>5
    <3> QED BY <3>2, <3>3
  <2> QED BY <1>4, <2>6 DEF NoneOtherChoosableAt
<1>5. CASE c > c0
  <2>1. c \in 0..(bb-1)
    BY <1>5
  <2>2. c # -1
    BY <2>1
  <2>3. PICK a3 \in Q : VotedFor(a3, c, vv)
    BY <1>1, <2>2
  <2>4. a3 \in Acceptor
    BY QuorumAssumption
  <2>5. c \in Ballot
    BY <2>1 DEF Ballot
  <2>6. SafeAt(c, vv)
    BY <2>3, <2>4, <2>5 DEF Inv, VotesSafe
  <2>7. c0 \in 0..(c-1)
    BY <1>5, <2>1
  <2> QED BY <2>6, <2>7 DEF SafeAt
<1> QED BY <1>3, <1>4, <1>5

-----------------------------------------------------------------------------

LEMMA InvNext ==
  ASSUME Inv, [Next]_<<votes, maxBal>>
  PROVE  Inv'
<1>0. TypeOK
  BY DEF Inv
<1>1. TypeOK'
  BY <1>0, NextTypeOK
<1>2. VotesSafe'
  <2> SUFFICES ASSUME NEW aa \in Acceptor, NEW bb \in Ballot, NEW vv \in Value,
                      VotedFor(aa, bb, vv)'
               PROVE  SafeAt(bb, vv)'
    BY DEF VotesSafe
  <2>1. CASE UNCHANGED <<votes, maxBal>>
    <3>1. votes' = votes
      BY <2>1
    <3>2. VotedFor(aa, bb, vv)
      BY <3>1 DEF VotedFor
    <3>3. SafeAt(bb, vv)
      BY <3>2 DEF Inv, VotesSafe
    <3> QED BY <3>3, <1>0, <2>1, SafeAtStable
  <2>2. ASSUME NEW a \in Acceptor, NEW b \in Ballot, IncreaseMaxBal(a, b)
        PROVE  SafeAt(bb, vv)'
    <3>1. votes' = votes
      BY <2>2 DEF IncreaseMaxBal
    <3>2. VotedFor(aa, bb, vv)
      BY <3>1 DEF VotedFor
    <3>3. SafeAt(bb, vv)
      BY <3>2 DEF Inv, VotesSafe
    <3>4. [Next]_<<votes, maxBal>>
      BY <2>2 DEF Next
    <3> QED BY <3>3, <1>0, <3>4, SafeAtStable
  <2>3. ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value, VoteFor(a, b, v)
        PROVE  SafeAt(bb, vv)'
    <3>1. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
      BY <2>3 DEF VoteFor
    <3>2. votes'[aa] = IF aa = a THEN votes[a] \cup {<<b, v>>} ELSE votes[aa]
      BY <3>1, <1>0 DEF TypeOK
    <3>3. <<bb, vv>> \in votes'[aa]
      BY DEF VotedFor
    <3>4. [Next]_<<votes, maxBal>>
      BY <2>3 DEF Next
    <3>5. CASE aa = a
      <4>1. <<bb, vv>> \in votes[a] \cup {<<b, v>>}
        BY <3>2, <3>3, <3>5
      <4>2. CASE <<bb, vv>> \in votes[a]
        <5>1. VotedFor(a, bb, vv)
          BY <4>2 DEF VotedFor
        <5>2. SafeAt(bb, vv)
          BY <5>1 DEF Inv, VotesSafe
        <5> QED BY <5>2, <1>0, <3>4, SafeAtStable
      <4>3. CASE <<bb, vv>> = <<b, v>>
        <5>1. bb = b /\ vv = v
          BY <4>3
        <5>2. PICK Q \in Quorum : ShowsSafeAt(Q, b, v)
          BY <2>3 DEF VoteFor
        <5>3. SafeAt(b, v)
          BY <5>2, ShowsSafetyLemma DEF Inv
        <5>4. SafeAt(bb, vv)
          BY <5>1, <5>3
        <5> QED BY <5>4, <1>0, <3>4, SafeAtStable
      <4> QED BY <4>1, <4>2, <4>3
    <3>6. CASE aa # a
      <4>1. <<bb, vv>> \in votes[aa]
        BY <3>2, <3>3, <3>6
      <4>2. VotedFor(aa, bb, vv)
        BY <4>1 DEF VotedFor
      <4>3. SafeAt(bb, vv)
        BY <4>2 DEF Inv, VotesSafe
      <4> QED BY <4>3, <1>0, <3>4, SafeAtStable
    <3> QED BY <3>5, <3>6
  <2> QED BY <2>1, <2>2, <2>3 DEF Next
<1>3. OneValuePerBallot'
  <2> SUFFICES ASSUME NEW a1 \in Acceptor, NEW a2 \in Acceptor,
                      NEW bx \in Ballot, NEW v1 \in Value, NEW v2 \in Value,
                      VotedFor(a1, bx, v1)', VotedFor(a2, bx, v2)'
               PROVE  v1 = v2
    BY DEF OneValuePerBallot
  <2>1. CASE UNCHANGED <<votes, maxBal>>
    <3>1. votes' = votes
      BY <2>1
    <3>2. VotedFor(a1, bx, v1)
      BY <3>1 DEF VotedFor
    <3>3. VotedFor(a2, bx, v2)
      BY <3>1 DEF VotedFor
    <3> QED BY <3>2, <3>3 DEF Inv, OneValuePerBallot
  <2>2. ASSUME NEW a \in Acceptor, NEW b \in Ballot, IncreaseMaxBal(a, b)
        PROVE  v1 = v2
    <3>1. votes' = votes
      BY <2>2 DEF IncreaseMaxBal
    <3>2. VotedFor(a1, bx, v1)
      BY <3>1 DEF VotedFor
    <3>3. VotedFor(a2, bx, v2)
      BY <3>1 DEF VotedFor
    <3> QED BY <3>2, <3>3 DEF Inv, OneValuePerBallot
  <2>3. ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value, VoteFor(a, b, v)
        PROVE  v1 = v2
    <3>1. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
      BY <2>3 DEF VoteFor
    <3>2. \A aa \in Acceptor : votes'[aa] = IF aa = a THEN votes[a] \cup {<<b, v>>} ELSE votes[aa]
      BY <3>1, <1>0 DEF TypeOK
    <3>3. ASSUME NEW aa \in Acceptor, NEW bb \in Ballot, NEW vv \in Value,
                 VotedFor(aa, bb, vv)'
          PROVE  VotedFor(aa, bb, vv) \/ (aa = a /\ bb = b /\ vv = v)
      <4>1. <<bb, vv>> \in votes'[aa]
        BY <3>3 DEF VotedFor
      <4>2. CASE aa = a
        <5>1. <<bb, vv>> \in votes[a] \cup {<<b, v>>}
          BY <3>2, <4>1, <4>2
        <5>2. CASE <<bb, vv>> \in votes[a]
          BY <4>2, <5>2 DEF VotedFor
        <5>3. CASE <<bb, vv>> = <<b, v>>
          <6>1. bb = b /\ vv = v
            BY <5>3
          <6> QED BY <4>2, <6>1
        <5> QED BY <5>1, <5>2, <5>3
      <4>3. CASE aa # a
        <5>1. votes'[aa] = votes[aa]
          BY <3>2, <4>3
        <5>2. <<bb, vv>> \in votes[aa]
          BY <4>1, <5>1
        <5> QED BY <5>2 DEF VotedFor
      <4> QED BY <4>2, <4>3
    <3>4. VotedFor(a1, bx, v1) \/ (a1 = a /\ bx = b /\ v1 = v)
      BY <3>3
    <3>5. VotedFor(a2, bx, v2) \/ (a2 = a /\ bx = b /\ v2 = v)
      BY <3>3
    <3>6. CASE VotedFor(a1, bx, v1) /\ VotedFor(a2, bx, v2)
      BY <3>6 DEF Inv, OneValuePerBallot
    <3>7. CASE VotedFor(a1, bx, v1) /\ (a2 = a /\ bx = b /\ v2 = v)
      <4>1. VotedFor(a1, b, v1)
        BY <3>7
      <4>2. v2 = v
        BY <3>7
      <4>3. CASE a1 = a
        <5>1. <<b, v1>> \in votes[a]
          BY <4>1, <4>3 DEF VotedFor
        <5>2. ~ \E vt \in votes[a] : vt[1] = b
          BY <2>3 DEF VoteFor
        <5>3. <<b, v1>>[1] = b
          OBVIOUS
        <5> QED BY <5>1, <5>2, <5>3
      <4>4. CASE a1 # a
        <5>1. \A vt \in votes[a1] : vt[1] = b => vt[2] = v
          BY <2>3, <4>4 DEF VoteFor
        <5>2. <<b, v1>> \in votes[a1]
          BY <4>1 DEF VotedFor
        <5>3. <<b, v1>>[1] = b
          OBVIOUS
        <5>4. <<b, v1>>[2] = v1
          OBVIOUS
        <5>5. v1 = v
          BY <5>1, <5>2, <5>3, <5>4
        <5> QED BY <5>5, <4>2
      <4> QED BY <4>3, <4>4
    <3>8. CASE (a1 = a /\ bx = b /\ v1 = v) /\ VotedFor(a2, bx, v2)
      <4>1. VotedFor(a2, b, v2)
        BY <3>8
      <4>2. v1 = v
        BY <3>8
      <4>3. CASE a2 = a
        <5>1. <<b, v2>> \in votes[a]
          BY <4>1, <4>3 DEF VotedFor
        <5>2. ~ \E vt \in votes[a] : vt[1] = b
          BY <2>3 DEF VoteFor
        <5>3. <<b, v2>>[1] = b
          OBVIOUS
        <5> QED BY <5>1, <5>2, <5>3
      <4>4. CASE a2 # a
        <5>1. \A vt \in votes[a2] : vt[1] = b => vt[2] = v
          BY <2>3, <4>4 DEF VoteFor
        <5>2. <<b, v2>> \in votes[a2]
          BY <4>1 DEF VotedFor
        <5>3. <<b, v2>>[1] = b
          OBVIOUS
        <5>4. <<b, v2>>[2] = v2
          OBVIOUS
        <5>5. v2 = v
          BY <5>1, <5>2, <5>3, <5>4
        <5> QED BY <5>5, <4>2
      <4> QED BY <4>3, <4>4
    <3>9. CASE (a1 = a /\ bx = b /\ v1 = v) /\ (a2 = a /\ bx = b /\ v2 = v)
      BY <3>9
    <3> QED BY <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
  <2> QED BY <2>1, <2>2, <2>3 DEF Next
<1> QED BY <1>1, <1>2, <1>3 DEF Inv

-----------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_<<votes, maxBal>> => Inv'
  BY InvNext
<1> QED BY <1>1, <1>2, PTL DEF Spec
----------------------------------------------------------------------------
----------------------------------------------------------------------------

=============================================================================
