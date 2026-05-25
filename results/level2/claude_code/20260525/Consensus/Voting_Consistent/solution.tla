------------------------------- MODULE Voting_Consistent -------------------------------
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


-----------------------------------------------------------------------------

    
-----------------------------------------------------------------------------
LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
BY QuorumAssumption

LEMMA AllSafeAtZero == \A v \in Value : SafeAt(0, v)
BY DEF SafeAt

THEOREM OneVoteThm == OneValuePerBallot => OneVote
BY DEF OneValuePerBallot, OneVote

THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value :
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
BY DEF ChosenAt, NoneOtherChoosableAt

LEMMA ChosenNotOther ==
  ASSUME OneVote, NEW b \in Ballot, NEW v \in Value, NEW w \in Value,
         ChosenAt(b, v), NoneOtherChoosableAt(b, w)
  PROVE  v = w
<1>1. PICK Q1 \in Quorum : \A a \in Q1 : VotedFor(a, b, v)
  BY DEF ChosenAt
<1>2. PICK Q2 \in Quorum : \A a \in Q2 : VotedFor(a, b, w) \/ CannotVoteAt(a, b)
  BY DEF NoneOtherChoosableAt
<1>3. Q1 \cap Q2 # {}
  BY QuorumAssumption
<1>4. PICK a \in Q1 \cap Q2 : TRUE
  BY <1>3
<1>5. a \in Acceptor
  BY <1>1, <1>4, QuorumAssumption
<1>6. VotedFor(a, b, v)
  BY <1>1, <1>4
<1>7. ~ CannotVoteAt(a, b)
  BY <1>6 DEF CannotVoteAt, DidNotVoteAt
<1>8. VotedFor(a, b, w)
  BY <1>2, <1>4, <1>7
<1>9. QED
  BY <1>5, <1>6, <1>8, OneVote DEF OneVote

THEOREM VotesSafeImpliesConsistency ==
   ASSUME VotesSafe, OneVote, chosen # {}
   PROVE  \E v \in Value : chosen = {v}
<1>1. PICK v \in chosen : TRUE
  OBVIOUS
<1>2. v \in Value
  BY <1>1 DEF chosen
<1>3. ASSUME NEW w \in chosen
      PROVE  w = v
  <2>0. w \in Value
    BY <1>3 DEF chosen
  <2>1. PICK b1 \in Ballot : ChosenAt(b1, v)
    BY <1>1 DEF chosen
  <2>2. PICK b2 \in Ballot : ChosenAt(b2, w)
    BY <1>3 DEF chosen
  <2>3. CASE b1 <= b2
    <3>1. NoneOtherChoosableAt(b1, w)
      <4>0. b1 = b2 \/ b1 < b2
        BY <2>3, <2>1, <2>2 DEF Ballot
      <4>1. CASE b1 = b2
        BY <4>1, <2>2, <2>0, ChoosableThm
      <4>2. CASE b1 < b2
        <5>1. PICK Qw \in Quorum : \A a \in Qw : VotedFor(a, b2, w)
          BY <2>2 DEF ChosenAt
        <5>2. PICK a \in Qw : VotedFor(a, b2, w)
          BY <5>1, QuorumNonEmpty
        <5>3. a \in Acceptor
          BY <5>2, <5>1, QuorumAssumption
        <5>4. SafeAt(b2, w)
          BY <5>2, <5>3, <2>0 DEF VotesSafe
        <5>5. b1 \in 0..(b2-1)
          BY <4>2, <2>1 DEF Ballot
        <5>6. QED
          BY <5>4, <5>5 DEF SafeAt
      <4>3. QED
        BY <4>0, <4>1, <4>2
    <3>2. QED
      BY <2>1, <3>1, <1>2, <2>0, ChosenNotOther
  <2>4. CASE b2 <= b1
    <3>1. NoneOtherChoosableAt(b2, v)
      <4>0. b2 = b1 \/ b2 < b1
        BY <2>4, <2>1, <2>2 DEF Ballot
      <4>1. CASE b2 = b1
        BY <4>1, <2>1, <1>2, ChoosableThm
      <4>2. CASE b2 < b1
        <5>1. PICK Qv \in Quorum : \A a \in Qv : VotedFor(a, b1, v)
          BY <2>1 DEF ChosenAt
        <5>2. PICK a \in Qv : VotedFor(a, b1, v)
          BY <5>1, QuorumNonEmpty
        <5>3. a \in Acceptor
          BY <5>2, <5>1, QuorumAssumption
        <5>4. SafeAt(b1, v)
          BY <5>2, <5>3, <1>2 DEF VotesSafe
        <5>5. b2 \in 0..(b1-1)
          BY <4>2, <2>2 DEF Ballot
        <5>6. QED
          BY <5>4, <5>5 DEF SafeAt
      <4>3. QED
        BY <4>0, <4>1, <4>2
    <3>2. QED
      BY <2>2, <3>1, <2>0, <1>2, ChosenNotOther
  <2>5. QED
    BY <2>3, <2>4, <2>1, <2>2 DEF Ballot
<1>4. chosen = {v}
  BY <1>1, <1>3
<1>5. QED
  BY <1>2, <1>4

THEOREM ShowsSafety ==
          TypeOK /\ VotesSafe /\ OneValuePerBallot =>
             \A Q \in Quorum, b \in Ballot, v \in Value :
               ShowsSafeAt(Q, b, v) => SafeAt(b, v)
<1> SUFFICES ASSUME TypeOK, VotesSafe, OneValuePerBallot,
                    NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
                    ShowsSafeAt(Q, b, v)
             PROVE  SafeAt(b, v)
  OBVIOUS
<1>1. \A a \in Q : maxBal[a] \geq b
  BY DEF ShowsSafeAt
<1>2. PICK c \in -1..(b-1) :
        /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
        /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
  BY DEF ShowsSafeAt
<1>3. Q \subseteq Acceptor
  BY QuorumAssumption
<1> SUFFICES ASSUME NEW cc \in 0..(b-1)
             PROVE  NoneOtherChoosableAt(cc, v)
  BY DEF SafeAt
<1>cov. cc \in (c+1)..(b-1) \/ cc \in 0..c
  BY <1>2 DEF Ballot
<1>4. CASE cc \in (c+1)..(b-1)
  <2>1. \A a \in Q : DidNotVoteAt(a, cc)
    BY <1>2, <1>4
  <2>2. \A a \in Q : CannotVoteAt(a, cc)
    <3>1. ASSUME NEW a \in Q PROVE CannotVoteAt(a, cc)
      <4>1. maxBal[a] \geq b
        BY <1>1, <3>1
      <4>2. maxBal[a] \in Int
        BY <1>3, <3>1 DEF TypeOK, Ballot
      <4>3. b > cc
        BY <1>4 DEF Ballot
      <4>4. maxBal[a] > cc
        BY <4>1, <4>2, <4>3 DEF Ballot
      <4>5. DidNotVoteAt(a, cc)
        BY <2>1, <3>1
      <4>6. QED
        BY <4>4, <4>5 DEF CannotVoteAt
    <3>2. QED
      BY <3>1
  <2>3. QED
    BY <2>2 DEF NoneOtherChoosableAt
<1>5. CASE cc \in 0..c
  <2>1. c # -1
    BY <1>5, <1>2
  <2>2. PICK a0 \in Q : VotedFor(a0, c, v)
    BY <1>2, <2>1
  <2>3. c \in Ballot
    BY <1>2, <2>1 DEF Ballot
  <2>4. a0 \in Acceptor
    BY <2>2, <1>3
  <2>5. SafeAt(c, v)
    BY <2>2, <2>3, <2>4, VotesSafe DEF VotesSafe
  <2>6. CASE cc < c
    <3>1. cc \in 0..(c-1)
      BY <1>5, <2>6 DEF Ballot
    <3>2. QED
      BY <2>5, <3>1 DEF SafeAt
  <2>7. CASE cc = c
    <3>1. \A a \in Q : VotedFor(a, cc, v) \/ CannotVoteAt(a, cc)
      <4>1. ASSUME NEW a \in Q
            PROVE  VotedFor(a, cc, v) \/ CannotVoteAt(a, cc)
        <5>1. CASE DidNotVoteAt(a, cc)
          <6>1. maxBal[a] \geq b
            BY <1>1, <4>1
          <6>2. b > cc
            BY DEF Ballot
          <6>3. maxBal[a] \in Int
            BY <1>3, <4>1 DEF TypeOK, Ballot
          <6>4. maxBal[a] > cc
            BY <6>1, <6>2, <6>3 DEF Ballot
          <6>5. QED
            BY <6>4, <5>1 DEF CannotVoteAt
        <5>2. CASE ~ DidNotVoteAt(a, cc)
          <6>1. PICK w \in Value : VotedFor(a, cc, w)
            BY <5>2 DEF DidNotVoteAt
          <6>2. VotedFor(a0, cc, v)
            BY <2>2, <2>7
          <6>3. a \in Acceptor
            BY <4>1, <1>3
          <6>4. w = v
            BY <6>1, <6>2, <6>3, <2>4, <2>3, <2>7, OneValuePerBallot
               DEF OneValuePerBallot
          <6>5. QED
            BY <6>1, <6>4
        <5>3. QED
          BY <5>1, <5>2
      <4>2. QED
        BY <4>1
    <3>2. QED
      BY <3>1 DEF NoneOtherChoosableAt
  <2>8. QED
    BY <2>6, <2>7, <1>5, <2>3 DEF Ballot
<1>6. QED
  BY <1>4, <1>5, <1>cov

LEMMA VotesGrow ==
  ASSUME TypeOK, Next, NEW a \in Acceptor
  PROVE  votes[a] \subseteq votes'[a]
<1>1. CASE \E a2 \in Acceptor, b2 \in Ballot : IncreaseMaxBal(a2, b2)
  BY <1>1 DEF IncreaseMaxBal
<1>2. CASE \E a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
  <2>1. PICK a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
    BY <1>2
  <2>2. votes' = [votes EXCEPT ![a2] = votes[a2] \cup {<<b2, v2>>}]
    BY <2>1 DEF VoteFor
  <2>3. CASE a = a2
    BY <2>2, <2>3, <2>1 DEF TypeOK
  <2>4. CASE a # a2
    BY <2>2, <2>4, <2>1 DEF TypeOK
  <2>5. QED
    BY <2>3, <2>4
<1>3. QED
  BY <1>1, <1>2 DEF Next

LEMMA CannotVoteStable ==
  ASSUME TypeOK, TypeOK', Next, NEW a \in Acceptor, NEW c \in Ballot,
         CannotVoteAt(a, c)
  PROVE  CannotVoteAt(a, c)'
<1>1. maxBal[a] > c
  BY DEF CannotVoteAt
<1>2. DidNotVoteAt(a, c)
  BY DEF CannotVoteAt
<1>3. maxBal[a] \in Int /\ maxBal'[a] \in Int
  BY DEF TypeOK, Ballot
<1> SUFFICES (maxBal'[a] > c) /\ DidNotVoteAt(a, c)'
  BY DEF CannotVoteAt
<1>4. CASE \E a2 \in Acceptor, b2 \in Ballot : IncreaseMaxBal(a2, b2)
  <2>1. PICK a2 \in Acceptor, b2 \in Ballot : IncreaseMaxBal(a2, b2)
    BY <1>4
  <2>2. maxBal' = [maxBal EXCEPT ![a2] = b2]
    BY <2>1 DEF IncreaseMaxBal
  <2>3. votes' = votes
    BY <2>1 DEF IncreaseMaxBal
  <2>4. b2 > maxBal[a2]
    BY <2>1 DEF IncreaseMaxBal
  <2>5. maxBal'[a] > c
    <3>1. CASE a = a2
      BY <2>2, <2>4, <3>1, <1>1, <1>3, <2>1 DEF TypeOK, Ballot, IncreaseMaxBal
    <3>2. CASE a # a2
      BY <2>2, <3>2, <1>1, <2>1 DEF TypeOK
    <3>3. QED
      BY <3>1, <3>2
  <2>6. DidNotVoteAt(a, c)'
    BY <2>3, <1>2 DEF DidNotVoteAt, VotedFor
  <2>7. QED
    BY <2>5, <2>6
<1>5. CASE \E a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
  <2>1. PICK a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
    BY <1>5
  <2>2. maxBal' = [maxBal EXCEPT ![a2] = b2]
    BY <2>1 DEF VoteFor
  <2>3. votes' = [votes EXCEPT ![a2] = votes[a2] \cup {<<b2, v2>>}]
    BY <2>1 DEF VoteFor
  <2>4. maxBal[a2] <= b2
    BY <2>1 DEF VoteFor
  <2>5. maxBal'[a] > c
    <3>1. CASE a = a2
      BY <2>2, <2>4, <3>1, <1>1, <1>3, <2>1 DEF TypeOK, Ballot, VoteFor
    <3>2. CASE a # a2
      BY <2>2, <3>2, <1>1, <2>1 DEF TypeOK
    <3>3. QED
      BY <3>1, <3>2
  <2>6. DidNotVoteAt(a, c)'
    <3>1. CASE a # a2
      <4>1. votes'[a] = votes[a]
        BY <2>3, <3>1, <2>1 DEF TypeOK
      <4>2. QED
        BY <4>1, <1>2 DEF DidNotVoteAt, VotedFor
    <3>2. CASE a = a2
      <4>1. c < b2
        BY <1>1, <2>4, <3>2, <1>3, <2>1 DEF TypeOK, Ballot, VoteFor
      <4>2. votes'[a] = votes[a] \cup {<<b2, v2>>}
        BY <2>3, <3>2, <2>1 DEF TypeOK
      <4>3. ASSUME NEW w \in Value, VotedFor(a, c, w)'
            PROVE  FALSE
        <5>1. <<c, w>> \in votes'[a]
          BY <4>3 DEF VotedFor
        <5>2. <<c, w>> \in votes[a] \/ <<c, w>> = <<b2, v2>>
          BY <5>1, <4>2
        <5>3. <<c, w>> # <<b2, v2>>
          BY <4>1
        <5>4. VotedFor(a, c, w)
          BY <5>2, <5>3 DEF VotedFor
        <5>5. QED
          BY <5>4, <1>2, <4>3 DEF DidNotVoteAt
      <4>4. QED
        BY <4>3 DEF DidNotVoteAt
    <3>3. QED
      BY <3>1, <3>2
  <2>7. QED
    BY <2>5, <2>6
<1>6. QED
  BY <1>4, <1>5 DEF Next

LEMMA SafeAtStable ==
  Inv /\ Next /\ TypeOK' =>
     \A bb \in Ballot, vv \in Value : SafeAt(bb, vv) => SafeAt(bb, vv)'
<1> SUFFICES ASSUME Inv, Next, TypeOK',
                    NEW bb \in Ballot, NEW vv \in Value, SafeAt(bb, vv)
             PROVE  SafeAt(bb, vv)'
  OBVIOUS
<1> USE DEF Inv
<1> SUFFICES ASSUME NEW c \in 0..(bb-1)
             PROVE  NoneOtherChoosableAt(c, vv)'
  BY DEF SafeAt
<1>0. c \in Ballot
  BY DEF Ballot
<1>1. NoneOtherChoosableAt(c, vv)
  BY DEF SafeAt
<1>2. PICK Q \in Quorum : \A a \in Q : VotedFor(a, c, vv) \/ CannotVoteAt(a, c)
  BY <1>1 DEF NoneOtherChoosableAt
<1>3. \A a \in Q : VotedFor(a, c, vv)' \/ CannotVoteAt(a, c)'
  <2>1. ASSUME NEW a \in Q
        PROVE  VotedFor(a, c, vv)' \/ CannotVoteAt(a, c)'
    <3>0. a \in Acceptor
      BY <2>1, QuorumAssumption
    <3>1. VotedFor(a, c, vv) \/ CannotVoteAt(a, c)
      BY <1>2, <2>1
    <3>2. CASE VotedFor(a, c, vv)
      <4>1. votes[a] \subseteq votes'[a]
        BY <3>0, VotesGrow
      <4>2. QED
        BY <3>2, <4>1 DEF VotedFor
    <3>3. CASE CannotVoteAt(a, c)
      BY <3>3, <3>0, <1>0, CannotVoteStable
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>2. QED
    BY <2>1
<1>4. QED
  BY <1>3 DEF NoneOtherChoosableAt

LEMMA NextTypeOK == TypeOK /\ Next => TypeOK'
<1> SUFFICES ASSUME TypeOK, Next PROVE TypeOK'
  OBVIOUS
<1>1. CASE \E a2 \in Acceptor, b2 \in Ballot : IncreaseMaxBal(a2, b2)
  <2>1. PICK a2 \in Acceptor, b2 \in Ballot : IncreaseMaxBal(a2, b2)
    BY <1>1
  <2>2. maxBal' = [maxBal EXCEPT ![a2] = b2]
    BY <2>1 DEF IncreaseMaxBal
  <2>3. votes' = votes
    BY <2>1 DEF IncreaseMaxBal
  <2>4. maxBal' \in [Acceptor -> Ballot \cup {-1}]
    BY <2>2, <2>1 DEF TypeOK
  <2>5. QED
    BY <2>3, <2>4 DEF TypeOK
<1>2. CASE \E a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
  <2>1. PICK a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
    BY <1>2
  <2>2. maxBal' = [maxBal EXCEPT ![a2] = b2]
    BY <2>1 DEF VoteFor
  <2>3. votes' = [votes EXCEPT ![a2] = votes[a2] \cup {<<b2, v2>>}]
    BY <2>1 DEF VoteFor
  <2>4. maxBal' \in [Acceptor -> Ballot \cup {-1}]
    BY <2>2, <2>1 DEF TypeOK
  <2>5. <<b2, v2>> \in Ballot \X Value
    BY <2>1
  <2>6. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]
    BY <2>3, <2>5, <2>1 DEF TypeOK
  <2>7. QED
    BY <2>4, <2>6 DEF TypeOK
<1>3. QED
  BY <1>1, <1>2 DEF Next

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv
  OBVIOUS
<1>1. TypeOK
  <2>1. votes = [a \in Acceptor |-> {}]
    BY DEF Init
  <2>2. maxBal = [a \in Acceptor |-> -1]
    BY DEF Init
  <2>3. votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    BY <2>1
  <2>4. maxBal \in [Acceptor -> Ballot \cup {-1}]
    BY <2>2
  <2>5. QED
    BY <2>3, <2>4 DEF TypeOK
<1>2. VotesSafe
  BY DEF Init, VotesSafe, VotedFor
<1>3. OneValuePerBallot
  BY DEF Init, OneValuePerBallot, VotedFor
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextOneValuePerBallot == Inv /\ Next => OneValuePerBallot'
<1> SUFFICES ASSUME Inv, Next PROVE OneValuePerBallot'
  OBVIOUS
<1> USE DEF Inv
<1>1. CASE \E a2 \in Acceptor, b2 \in Ballot : IncreaseMaxBal(a2, b2)
  BY <1>1 DEF IncreaseMaxBal, OneValuePerBallot, VotedFor
<1>2. CASE \E a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
  <2>1. PICK a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
    BY <1>2
  <2>2. votes' = [votes EXCEPT ![a2] = votes[a2] \cup {<<b2, v2>>}]
    BY <2>1 DEF VoteFor
  <2>P1. \A vt \in votes[a2] : vt[1] # b2
    BY <2>1 DEF VoteFor
  <2>P2. \A cc \in Acceptor \ {a2} : \A vt \in votes[cc] : (vt[1] = b2) => (vt[2] = v2)
    BY <2>1 DEF VoteFor
  <2>D. ASSUME NEW x \in Acceptor, NEW d \in Ballot, NEW vd \in Value,
               VotedFor(x, d, vd)'
        PROVE  VotedFor(x, d, vd) \/ (x = a2 /\ d = b2 /\ vd = v2)
    <3>1. <<d, vd>> \in votes'[x]
      BY <2>D DEF VotedFor
    <3>2. CASE x = a2
      <4>1. votes'[x] = votes[a2] \cup {<<b2, v2>>}
        BY <2>2, <3>2, <2>1 DEF TypeOK
      <4>2. <<d, vd>> \in votes[a2] \/ <<d, vd>> = <<b2, v2>>
        BY <3>1, <4>1
      <4>3. QED
        BY <4>2, <3>2 DEF VotedFor
    <3>3. CASE x # a2
      <4>1. votes'[x] = votes[x]
        BY <2>2, <3>3, <2>1 DEF TypeOK
      <4>2. QED
        BY <3>1, <4>1 DEF VotedFor
    <3>4. QED
      BY <3>2, <3>3
  <2> SUFFICES ASSUME NEW a1 \in Acceptor, NEW aa2 \in Acceptor, NEW bb \in Ballot,
                      NEW v1 \in Value, NEW v2x \in Value,
                      VotedFor(a1, bb, v1)', VotedFor(aa2, bb, v2x)'
               PROVE  v1 = v2x
    BY DEF OneValuePerBallot
  <2>X. VotedFor(a1, bb, v1) \/ (a1 = a2 /\ bb = b2 /\ v1 = v2)
    BY <2>D
  <2>Y. VotedFor(aa2, bb, v2x) \/ (aa2 = a2 /\ bb = b2 /\ v2x = v2)
    BY <2>D
  <2>3. CASE VotedFor(a1, bb, v1) /\ VotedFor(aa2, bb, v2x)
    BY <2>3, OneValuePerBallot DEF OneValuePerBallot
  <2>4. CASE (a1 = a2 /\ bb = b2 /\ v1 = v2) /\ VotedFor(aa2, bb, v2x)
    <3>1. VotedFor(aa2, b2, v2x)
      BY <2>4
    <3>2. <<b2, v2x>> \in votes[aa2]
      BY <3>1 DEF VotedFor
    <3>3. aa2 # a2
      BY <3>2, <2>P1
    <3>4. v2x = v2
      BY <3>2, <3>3, <2>P2
    <3>5. QED
      BY <2>4, <3>4
  <2>5. CASE VotedFor(a1, bb, v1) /\ (aa2 = a2 /\ bb = b2 /\ v2x = v2)
    <3>1. VotedFor(a1, b2, v1)
      BY <2>5
    <3>2. <<b2, v1>> \in votes[a1]
      BY <3>1 DEF VotedFor
    <3>3. a1 # a2
      BY <3>2, <2>P1
    <3>4. v1 = v2
      BY <3>2, <3>3, <2>P2
    <3>5. QED
      BY <2>5, <3>4
  <2>6. CASE (a1 = a2 /\ bb = b2 /\ v1 = v2) /\ (aa2 = a2 /\ bb = b2 /\ v2x = v2)
    BY <2>6
  <2>7. QED
    BY <2>X, <2>Y, <2>3, <2>4, <2>5, <2>6
<1>3. QED
  BY <1>1, <1>2 DEF Next

LEMMA NextVotesSafe == Inv /\ Next /\ TypeOK' => VotesSafe'
<1> SUFFICES ASSUME Inv, Next, TypeOK',
                    NEW a1 \in Acceptor, NEW bb \in Ballot, NEW vv \in Value,
                    VotedFor(a1, bb, vv)'
             PROVE  SafeAt(bb, vv)'
  BY DEF VotesSafe
<1> USE DEF Inv
<1>1. CASE VotedFor(a1, bb, vv)
  <2>1. SafeAt(bb, vv)
    BY <1>1 DEF VotesSafe
  <2>2. QED
    BY <2>1, SafeAtStable
<1>2. CASE ~ VotedFor(a1, bb, vv)
  <2>1. CASE \E a2 \in Acceptor, b2 \in Ballot : IncreaseMaxBal(a2, b2)
    <3>1. votes' = votes
      BY <2>1 DEF IncreaseMaxBal
    <3>2. VotedFor(a1, bb, vv)
      BY <3>1 DEF VotedFor
    <3>3. QED
      BY <3>2, <1>2
  <2>2. CASE \E a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
    <3>1. PICK a2 \in Acceptor, b2 \in Ballot, v2 \in Value : VoteFor(a2, b2, v2)
      BY <2>2
    <3>2. votes' = [votes EXCEPT ![a2] = votes[a2] \cup {<<b2, v2>>}]
      BY <3>1 DEF VoteFor
    <3>3. <<bb, vv>> \in votes'[a1]
      BY DEF VotedFor
    <3>4. ~ (<<bb, vv>> \in votes[a1])
      BY <1>2 DEF VotedFor
    <3>5. a1 = a2 /\ <<bb, vv>> = <<b2, v2>>
      <4>1. CASE a1 = a2
        <5>1. votes'[a1] = votes[a1] \cup {<<b2, v2>>}
          BY <3>2, <4>1, <3>1 DEF TypeOK
        <5>2. <<bb, vv>> = <<b2, v2>>
          BY <3>3, <5>1, <3>4
        <5>3. QED
          BY <4>1, <5>2
      <4>2. CASE a1 # a2
        <5>1. votes'[a1] = votes[a1]
          BY <3>2, <4>2, <3>1 DEF TypeOK
        <5>2. QED
          BY <3>3, <5>1, <3>4
      <4>3. QED
        BY <4>1, <4>2
    <3>6. bb = b2 /\ vv = v2
      BY <3>5
    <3>7. PICK Q \in Quorum : ShowsSafeAt(Q, b2, v2)
      BY <3>1 DEF VoteFor
    <3>8. SafeAt(b2, v2)
      BY <3>7, <3>1, ShowsSafety
    <3>9. SafeAt(bb, vv)
      BY <3>8, <3>6
    <3>10. QED
      BY <3>9, SafeAtStable
  <2>3. QED
    BY <2>1, <2>2 DEF Next
<1>3. QED
  BY <1>1, <1>2

THEOREM Invariant == Spec => []Inv
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_<<votes, maxBal>> => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_<<votes, maxBal>>
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE Next
    <3>1. TypeOK'
      BY <2>1, NextTypeOK DEF Inv
    <3>2. OneValuePerBallot'
      BY <2>1, NextOneValuePerBallot
    <3>3. VotesSafe'
      BY <2>1, <3>1, NextVotesSafe
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF Inv
  <2>2. CASE UNCHANGED <<votes, maxBal>>
    <3>1. votes' = votes /\ maxBal' = maxBal
      BY <2>2
    <3>2. QED
      BY <3>1 DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, VotedFor, SafeAt,
                NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM ConsistencyFromInv == Inv => Consistency
<1> SUFFICES ASSUME Inv PROVE Consistency
  OBVIOUS
<1>1. CASE chosen = {}
  BY <1>1 DEF Consistency
<1>2. CASE chosen # {}
  <2>1. OneVote
    BY OneVoteThm DEF Inv
  <2>2. VotesSafe
    BY DEF Inv
  <2>3. \E v \in Value : chosen = {v}
    BY <2>1, <2>2, <1>2, VotesSafeImpliesConsistency
  <2>4. QED
    BY <2>3 DEF Consistency
<1>3. QED
  BY <1>1, <1>2
-----------------------------------------------------------------------------
----------------------------------------------------------------------------
THEOREM Consistent == Spec => []Consistency
<1>1. Spec => []Inv
  BY Invariant
<1>2. Inv => Consistency
  BY ConsistencyFromInv
<1>3. QED
  BY <1>1, <1>2, PTL
----------------------------------------------------------------------------
C == INSTANCE Consensus \* WITH chosen <- chosen

=============================================================================