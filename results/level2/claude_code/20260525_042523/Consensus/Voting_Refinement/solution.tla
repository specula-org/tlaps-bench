------------------------------- MODULE Voting_Refinement -------------------------------
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
----------------------------------------------------------------------------
----------------------------------------------------------------------------
LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
  BY QuorumAssumption

LEMMA AllSafeAtZero == \A v \in Value : SafeAt(0, v)
  BY DEF SafeAt

LEMMA OneVoteThm == OneValuePerBallot => OneVote
  BY DEF OneValuePerBallot, OneVote

LEMMA ChoosableThm ==
  \A b \in Ballot, v \in Value : ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
  BY DEF ChosenAt, NoneOtherChoosableAt

LEMMA ChosenConsistent ==
  ASSUME VotesSafe, OneVote,
         NEW b1 \in Ballot, NEW v1 \in Value,
         NEW b2 \in Ballot, NEW v2 \in Value,
         ChosenAt(b1, v1), ChosenAt(b2, v2), b1 =< b2
  PROVE  v1 = v2
<1> USE DEF Ballot
<1>1. PICK Q2 \in Quorum : \A a \in Q2 : VotedFor(a, b2, v2)
  BY DEF ChosenAt
<1>2. PICK a2 \in Q2 : VotedFor(a2, b2, v2)
  BY QuorumNonEmpty, <1>1
<1>3. a2 \in Acceptor
  BY <1>2, QuorumAssumption
<1>4. SafeAt(b2, v2)
  BY <1>2, <1>3 DEF VotesSafe
<1>5. PICK Q1 \in Quorum : \A a \in Q1 : VotedFor(a, b1, v1)
  BY DEF ChosenAt
<1>6. CASE b1 = b2
  <2>1. Q1 \cap Q2 # {}
    BY QuorumAssumption
  <2>2. PICK a \in Q1 \cap Q2 : TRUE
    BY <2>1
  <2>2a. a \in Acceptor
    BY <2>2, QuorumAssumption
  <2>3. VotedFor(a, b1, v1)
    BY <2>2, <1>5
  <2>4. VotedFor(a, b1, v2)
    BY <2>2, <1>1, <1>6 DEF VotedFor
  <2> QED
    BY <2>2a, <2>3, <2>4 DEF OneVote
<1>7. CASE b1 # b2
  <2>0. b1 < b2
    BY <1>7
  <2>1. b1 \in 0..(b2 - 1)
    BY <2>0
  <2>2. NoneOtherChoosableAt(b1, v2)
    BY <1>4, <2>1 DEF SafeAt
  <2>3. PICK Q3 \in Quorum : \A a \in Q3 : VotedFor(a, b1, v2) \/ CannotVoteAt(a, b1)
    BY <2>2 DEF NoneOtherChoosableAt
  <2>4. Q1 \cap Q3 # {}
    BY QuorumAssumption
  <2>5. PICK a \in Q1 \cap Q3 : TRUE
    BY <2>4
  <2>5a. a \in Acceptor
    BY <2>5, QuorumAssumption
  <2>6. VotedFor(a, b1, v1)
    BY <2>5, <1>5
  <2>7. VotedFor(a, b1, v2) \/ CannotVoteAt(a, b1)
    BY <2>5, <2>3
  <2>8. ~ CannotVoteAt(a, b1)
    BY <2>6 DEF CannotVoteAt, DidNotVoteAt
  <2>9. VotedFor(a, b1, v2)
    BY <2>7, <2>8
  <2> QED
    BY <2>5a, <2>6, <2>9 DEF OneVote
<1> QED
  BY <1>6, <1>7

LEMMA VotesSafeImpliesConsistency ==
  ASSUME VotesSafe, OneVote, chosen # {}
  PROVE  \E v \in Value : chosen = {v}
<1>1. PICK w \in chosen : TRUE
  OBVIOUS
<1>2. w \in Value
  BY <1>1 DEF chosen
<1>3. PICK bw \in Ballot : ChosenAt(bw, w)
  BY <1>1 DEF chosen
<1>4. \A v \in chosen : v = w
  <2> TAKE v \in chosen
  <2>1. v \in Value
    BY DEF chosen
  <2>2. PICK bv \in Ballot : ChosenAt(bv, v)
    BY DEF chosen
  <2>3. CASE bv =< bw
    BY <2>3, <2>2, <1>3, <2>1, <1>2, ChosenConsistent
  <2>4. CASE ~ (bv =< bw)
    <3>1. bw =< bv
      BY <2>4 DEF Ballot
    <3> QED
      BY <3>1, <1>3, <2>2, <1>2, <2>1, ChosenConsistent
  <2> QED
    BY <2>3, <2>4
<1>5. chosen = {w}
  BY <1>1, <1>4
<1> QED
  BY <1>2, <1>5

LEMMA InvConsistency == Inv => Consistency
<1> SUFFICES ASSUME Inv, chosen # {}
             PROVE  \E v \in Value : chosen = {v}
  BY DEF Consistency
<1>1. VotesSafe
  BY DEF Inv
<1>2. OneVote
  BY OneVoteThm DEF Inv
<1> QED
  BY <1>1, <1>2, VotesSafeImpliesConsistency

LEMMA ShowsSafety ==
  TypeOK /\ VotesSafe /\ OneValuePerBallot =>
    \A Q \in Quorum, b \in Ballot, v \in Value :
      ShowsSafeAt(Q, b, v) => SafeAt(b, v)
<1> SUFFICES ASSUME TypeOK, VotesSafe, OneValuePerBallot,
                    NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
                    ShowsSafeAt(Q, b, v)
             PROVE  SafeAt(b, v)
  OBVIOUS
<1> USE DEF Ballot
<1>Q. Q \subseteq Acceptor
  BY QuorumAssumption
<1>mb. \A a \in Q : maxBal[a] \geq b
  BY DEF ShowsSafeAt
<1>c. PICK c \in -1..(b-1) :
        /\ (c # -1) => (\E a \in Q : VotedFor(a, c, v))
        /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
  BY DEF ShowsSafeAt
<1> SUFFICES ASSUME NEW e \in 0..(b-1)
             PROVE  NoneOtherChoosableAt(e, v)
  BY DEF SafeAt
<1>en. e \in Nat
  OBVIOUS
<1>1. CASE e \in (c+1)..(b-1)
  <2>1. \A a \in Q : CannotVoteAt(a, e)
    <3> TAKE a \in Q
    <3>1. a \in Acceptor
      BY <1>Q
    <3>2. DidNotVoteAt(a, e)
      BY <1>1, <1>c
    <3>3. maxBal[a] \geq b
      BY <1>mb
    <3>4. maxBal[a] \in Int
      BY <3>1, TypeOK DEF TypeOK
    <3>5. e < b
      BY <1>1
    <3>6. maxBal[a] > e
      BY <3>3, <3>4, <3>5
    <3> QED
      BY <3>2, <3>6 DEF CannotVoteAt
  <2> QED
    BY <2>1 DEF NoneOtherChoosableAt
<1>2. CASE e = c
  <2>1. c # -1
    BY <1>2
  <2>2. PICK a0 \in Q : VotedFor(a0, c, v)
    BY <1>c, <2>1
  <2>3. \A a \in Q : VotedFor(a, e, v) \/ CannotVoteAt(a, e)
    <3> TAKE a \in Q
    <3>1. a \in Acceptor
      BY <1>Q
    <3>2. maxBal[a] \geq b
      BY <1>mb
    <3>3. maxBal[a] \in Int
      BY <3>1, TypeOK DEF TypeOK
    <3>4. e < b
      BY <1>2
    <3>5. maxBal[a] > e
      BY <3>2, <3>3, <3>4
    <3>6. CASE DidNotVoteAt(a, e)
      BY <3>5, <3>6 DEF CannotVoteAt
    <3>7. CASE ~ DidNotVoteAt(a, e)
      <4>1. PICK w \in Value : VotedFor(a, e, w)
        BY <3>7 DEF DidNotVoteAt
      <4>2. VotedFor(a0, e, v)
        BY <2>2, <1>2
      <4>3. a0 \in Acceptor
        BY <1>Q, <2>2
      <4>4. w = v
        BY <4>1, <4>2, <3>1, <4>3, <1>en DEF OneValuePerBallot
      <4> QED
        BY <4>1, <4>4
    <3> QED
      BY <3>6, <3>7
  <2> QED
    BY <2>3 DEF NoneOtherChoosableAt
<1>3. CASE e \in 0..(c-1)
  <2>1. c # -1
    BY <1>3
  <2>2. PICK a0 \in Q : VotedFor(a0, c, v)
    BY <1>c, <2>1
  <2>3. a0 \in Acceptor
    BY <1>Q, <2>2
  <2>4. c \in Ballot
    BY <2>1, <1>c
  <2>5. SafeAt(c, v)
    BY <2>2, <2>3, <2>4 DEF VotesSafe
  <2> QED
    BY <2>5, <1>3 DEF SafeAt
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA VotesGrow ==
  ASSUME TypeOK, Next, NEW a \in Acceptor
  PROVE  votes[a] \subseteq votes'[a]
<1>1. PICK a0 \in Acceptor, b0 \in Ballot :
        IncreaseMaxBal(a0, b0) \/ (\E v0 \in Value : VoteFor(a0, b0, v0))
  BY DEF Next
<1>2. CASE IncreaseMaxBal(a0, b0)
  BY <1>2 DEF IncreaseMaxBal
<1>3. CASE \E v0 \in Value : VoteFor(a0, b0, v0)
  <2>1. PICK v0 \in Value : VoteFor(a0, b0, v0)
    BY <1>3
  <2>2. votes' = [votes EXCEPT ![a0] = votes[a0] \cup {<<b0, v0>>}]
    BY <2>1 DEF VoteFor
  <2> QED
    BY <2>2, TypeOK DEF TypeOK
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA MaxBalGrows ==
  ASSUME TypeOK, Next, NEW a \in Acceptor
  PROVE  maxBal[a] =< maxBal'[a]
<1> USE DEF Ballot
<1>1. PICK a0 \in Acceptor, b0 \in Ballot :
        IncreaseMaxBal(a0, b0) \/ (\E v0 \in Value : VoteFor(a0, b0, v0))
  BY DEF Next
<1>2. CASE IncreaseMaxBal(a0, b0)
  <2>1. b0 > maxBal[a0] /\ maxBal' = [maxBal EXCEPT ![a0] = b0]
    BY <1>2 DEF IncreaseMaxBal
  <2> QED
    BY <2>1, TypeOK DEF TypeOK
<1>3. CASE \E v0 \in Value : VoteFor(a0, b0, v0)
  <2>1. PICK v0 \in Value : VoteFor(a0, b0, v0)
    BY <1>3
  <2>2. maxBal[a0] =< b0 /\ maxBal' = [maxBal EXCEPT ![a0] = b0]
    BY <2>1 DEF VoteFor
  <2> QED
    BY <2>2, TypeOK DEF TypeOK
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA NewVoteCond ==
  ASSUME TypeOK, Next,
         NEW a \in Acceptor, NEW bb \in Ballot, NEW w \in Value,
         VotedFor(a, bb, w)', ~ VotedFor(a, bb, w)
  PROVE  maxBal[a] =< bb
<1> USE DEF Ballot
<1>1. PICK a0 \in Acceptor, b0 \in Ballot :
        IncreaseMaxBal(a0, b0) \/ (\E v0 \in Value : VoteFor(a0, b0, v0))
  BY DEF Next
<1>2. CASE IncreaseMaxBal(a0, b0)
  BY <1>2 DEF IncreaseMaxBal, VotedFor
<1>3. CASE \E v0 \in Value : VoteFor(a0, b0, v0)
  <2>1. PICK v0 \in Value : VoteFor(a0, b0, v0)
    BY <1>3
  <2>2. votes' = [votes EXCEPT ![a0] = votes[a0] \cup {<<b0, v0>>}]
    BY <2>1 DEF VoteFor
  <2>3. maxBal[a0] =< b0
    BY <2>1 DEF VoteFor
  <2>4. <<bb, w>> \in votes'[a]
    BY DEF VotedFor
  <2>5. <<bb, w>> \notin votes[a]
    BY DEF VotedFor
  <2>6. a = a0 /\ <<bb, w>> = <<b0, v0>>
    BY <2>2, <2>4, <2>5, TypeOK DEF TypeOK
  <2>7. bb = b0
    BY <2>6
  <2> QED
    BY <2>3, <2>6, <2>7
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA SafeAtStable ==
  Inv /\ Next /\ TypeOK' =>
    \A bb \in Ballot, vv \in Value : SafeAt(bb, vv) => SafeAt(bb, vv)'
<1> SUFFICES ASSUME Inv, Next, TypeOK',
                    NEW bb \in Ballot, NEW vv \in Value, SafeAt(bb, vv)
             PROVE  SafeAt(bb, vv)'
  OBVIOUS
<1> USE DEF Ballot
<1>to. TypeOK
  BY DEF Inv
<1> SUFFICES ASSUME NEW c \in 0..(bb-1)
             PROVE  NoneOtherChoosableAt(c, vv)'
  BY DEF SafeAt
<1>cn. c \in Nat
  OBVIOUS
<1>1. NoneOtherChoosableAt(c, vv)
  BY DEF SafeAt
<1>2. PICK QQ \in Quorum : \A a \in QQ : VotedFor(a, c, vv) \/ CannotVoteAt(a, c)
  BY <1>1 DEF NoneOtherChoosableAt
<1>3. \A a \in QQ : VotedFor(a, c, vv)' \/ CannotVoteAt(a, c)'
  <2> TAKE a \in QQ
  <2>0. a \in Acceptor
    BY QuorumAssumption
  <2>1. VotedFor(a, c, vv) \/ CannotVoteAt(a, c)
    BY <1>2
  <2>2. CASE VotedFor(a, c, vv)
    <3>1. votes[a] \subseteq votes'[a]
      BY VotesGrow, <1>to, <2>0
    <3>2. VotedFor(a, c, vv)'
      BY <2>2, <3>1 DEF VotedFor
    <3> QED
      BY <3>2
  <2>3. CASE CannotVoteAt(a, c)
    <3>1. maxBal[a] > c /\ DidNotVoteAt(a, c)
      BY <2>3 DEF CannotVoteAt
    <3>2. maxBal[a] =< maxBal'[a]
      BY MaxBalGrows, <1>to, <2>0
    <3>3. maxBal[a] \in Int
      BY <2>0, <1>to DEF TypeOK
    <3>4. maxBal'[a] \in Int
      BY <2>0, TypeOK' DEF TypeOK
    <3>6. maxBal'[a] > c
      BY <3>1, <3>2, <3>3, <3>4, <1>cn
    <3>7. DidNotVoteAt(a, c)'
      <4> SUFFICES ASSUME NEW ww \in Value, VotedFor(a, c, ww)'
                   PROVE  FALSE
        BY DEF DidNotVoteAt
      <4>1. ~ VotedFor(a, c, ww)
        BY <3>1 DEF DidNotVoteAt
      <4>2. maxBal[a] =< c
        BY NewVoteCond, <1>to, <2>0, <4>1, <1>cn
      <4> QED
        BY <3>1, <3>3, <4>2
    <3> QED
      BY <3>6, <3>7 DEF CannotVoteAt
  <2> QED
    BY <2>1, <2>2, <2>3
<1> QED
  BY <1>3 DEF NoneOtherChoosableAt

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv
  OBVIOUS
<1>1. TypeOK
  BY DEF Init, TypeOK
<1>2. VotesSafe
  <2> SUFFICES ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value,
                      VotedFor(a, b, v)
               PROVE  SafeAt(b, v)
    BY DEF VotesSafe
  <2>1. votes[a] = {}
    BY DEF Init
  <2>2. ~ VotedFor(a, b, v)
    BY <2>1 DEF VotedFor
  <2> QED
    BY <2>2
<1>3. OneValuePerBallot
  <2> SUFFICES ASSUME NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW b \in Ballot,
                      NEW v1 \in Value, NEW v2 \in Value,
                      VotedFor(a1, b, v1), VotedFor(a2, b, v2)
               PROVE  v1 = v2
    BY DEF OneValuePerBallot
  <2>1. votes[a1] = {}
    BY DEF Init
  <2>2. ~ VotedFor(a1, b, v1)
    BY <2>1 DEF VotedFor
  <2> QED
    BY <2>2
<1> QED
  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_<<votes, maxBal>> => Inv'
<1> SUFFICES ASSUME Inv, [Next]_<<votes, maxBal>>
             PROVE  Inv'
  OBVIOUS
<1> USE DEF Ballot
<1>1. CASE <<votes, maxBal>>' = <<votes, maxBal>>
  <2>1. votes' = votes /\ maxBal' = maxBal
    BY <1>1
  <2> QED
    BY <2>1 DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, SafeAt,
              NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt, VotedFor
<1>2. CASE Next
  <2>tok. TypeOK
    BY DEF Inv
  <2>pk. PICK a0 \in Acceptor, b0 \in Ballot :
           IncreaseMaxBal(a0, b0) \/ (\E v0 \in Value : VoteFor(a0, b0, v0))
    BY <1>2 DEF Next
  <2>1. TypeOK'
    <3>1. CASE IncreaseMaxBal(a0, b0)
      BY <3>1, <2>tok DEF TypeOK, IncreaseMaxBal
    <3>2. CASE \E v0 \in Value : VoteFor(a0, b0, v0)
      <4>1. PICK v0 \in Value : VoteFor(a0, b0, v0)
        BY <3>2
      <4>2. votes' = [votes EXCEPT ![a0] = votes[a0] \cup {<<b0, v0>>}]
            /\ maxBal' = [maxBal EXCEPT ![a0] = b0]
        BY <4>1 DEF VoteFor
      <4> QED
        BY <4>2, <2>tok DEF TypeOK
    <3> QED
      BY <2>pk, <3>1, <3>2
  <2>ss. \A xb \in Ballot, xv \in Value : SafeAt(xb, xv) => SafeAt(xb, xv)'
    BY SafeAtStable, <1>2, <2>1 DEF Inv
  <2>2. OneValuePerBallot'
    <3>1. CASE IncreaseMaxBal(a0, b0)
      BY <3>1, <2>tok DEF Inv, OneValuePerBallot, VotedFor, IncreaseMaxBal
    <3>2. CASE \E v0 \in Value : VoteFor(a0, b0, v0)
      <4>1. PICK v0 \in Value : VoteFor(a0, b0, v0)
        BY <3>2
      <4>2. votes' = [votes EXCEPT ![a0] = votes[a0] \cup {<<b0, v0>>}]
        BY <4>1 DEF VoteFor
      <4>P1. \A vt \in votes[a0] : vt[1] # b0
        BY <4>1 DEF VoteFor
      <4>P2. \A cc \in Acceptor \ {a0} : \A vt \in votes[cc] : (vt[1] = b0) => (vt[2] = v0)
        BY <4>1 DEF VoteFor
      <4> SUFFICES ASSUME NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW bq \in Ballot,
                          NEW v1 \in Value, NEW v2 \in Value,
                          VotedFor(a1, bq, v1)', VotedFor(a2, bq, v2)'
                   PROVE  v1 = v2
        BY DEF OneValuePerBallot
      <4>3. ASSUME NEW aa \in Acceptor, NEW vx \in Value, VotedFor(aa, b0, vx)'
            PROVE  vx = v0
        <5>1. <<b0, vx>> \in votes'[aa]
          BY <4>3 DEF VotedFor
        <5>2. CASE aa = a0
          <6>1. <<b0, vx>> \in votes[a0] \cup {<<b0, v0>>}
            BY <5>1, <4>2, <5>2, <2>tok DEF TypeOK
          <6>2. <<b0, vx>> \notin votes[a0]
            BY <4>P1
          <6> QED
            BY <6>1, <6>2
        <5>3. CASE aa # a0
          <6>1. votes'[aa] = votes[aa]
            BY <4>2, <5>3, <2>tok DEF TypeOK
          <6>2. <<b0, vx>> \in votes[aa]
            BY <5>1, <6>1
          <6> QED
            BY <6>2, <4>P2, <5>3
        <5> QED
          BY <5>2, <5>3
      <4>4. CASE bq = b0
        <5>1. v1 = v0
          BY <4>3, <4>4
        <5>2. v2 = v0
          BY <4>3, <4>4
        <5> QED
          BY <5>1, <5>2
      <4>5. CASE bq # b0
        <5>1. VotedFor(a1, bq, v1)
          BY <4>2, <4>5, <2>tok DEF TypeOK, VotedFor
        <5>2. VotedFor(a2, bq, v2)
          BY <4>2, <4>5, <2>tok DEF TypeOK, VotedFor
        <5> QED
          BY <5>1, <5>2, <2>tok DEF Inv, OneValuePerBallot
      <4> QED
        BY <4>4, <4>5
    <3> QED
      BY <2>pk, <3>1, <3>2
  <2>3. VotesSafe'
    <3> SUFFICES ASSUME NEW a \in Acceptor, NEW bq \in Ballot, NEW v \in Value,
                        VotedFor(a, bq, v)'
                 PROVE  SafeAt(bq, v)'
      BY DEF VotesSafe
    <3>1. CASE IncreaseMaxBal(a0, b0)
      <4>1. votes' = votes
        BY <3>1 DEF IncreaseMaxBal
      <4>2. VotedFor(a, bq, v)
        BY <4>1 DEF VotedFor
      <4>3. SafeAt(bq, v)
        BY <4>2, <2>tok DEF Inv, VotesSafe
      <4> QED
        BY <4>3, <2>ss
    <3>2. CASE \E v0 \in Value : VoteFor(a0, b0, v0)
      <4>1. PICK v0 \in Value : VoteFor(a0, b0, v0)
        BY <3>2
      <4>2. votes' = [votes EXCEPT ![a0] = votes[a0] \cup {<<b0, v0>>}]
        BY <4>1 DEF VoteFor
      <4>3. <<bq, v>> \in votes'[a]
        BY DEF VotedFor
      <4>4. CASE <<bq, v>> \in votes[a]
        <5>1. VotedFor(a, bq, v)
          BY <4>4 DEF VotedFor
        <5>2. SafeAt(bq, v)
          BY <5>1, <2>tok DEF Inv, VotesSafe
        <5> QED
          BY <5>2, <2>ss
      <4>5. CASE <<bq, v>> \notin votes[a]
        <5>1. a = a0 /\ <<bq, v>> = <<b0, v0>>
          BY <4>2, <4>3, <4>5, <2>tok DEF TypeOK
        <5>2. bq = b0 /\ v = v0
          BY <5>1
        <5>3. PICK QQ \in Quorum : ShowsSafeAt(QQ, b0, v0)
          BY <4>1 DEF VoteFor
        <5>4. SafeAt(b0, v0)
          BY <5>3, ShowsSafety, <2>tok DEF Inv
        <5>5. SafeAt(bq, v)
          BY <5>4, <5>2
        <5> QED
          BY <5>5, <2>ss
      <4> QED
        BY <4>4, <4>5
    <3> QED
      BY <2>pk, <3>1, <3>2
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Inv
<1> QED
  BY <1>1, <1>2 DEF Next

LEMMA Invariant == Spec => []Inv
  BY InitInv, NextInv, PTL DEF Spec

LEMMA Consistent == Spec => []Consistency
  BY Invariant, InvConsistency, PTL

-----------------------------------------------------------------------------
C == INSTANCE Consensus \* WITH chosen <- chosen

LEMMA InitC == Init => C!Init
<1> SUFFICES ASSUME Init PROVE chosen = {}
  BY DEF C!Init
<1>1. \A v \in Value : ~ (\E b \in Ballot : ChosenAt(b, v))
  <2> TAKE v \in Value
  <2> SUFFICES ASSUME NEW b \in Ballot, ChosenAt(b, v) PROVE FALSE
    OBVIOUS
  <2>1. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
    BY DEF ChosenAt
  <2>2. Q # {}
    BY QuorumNonEmpty
  <2>3. PICK a \in Q : TRUE
    BY <2>2
  <2>4. a \in Acceptor
    BY <2>3, QuorumAssumption
  <2>5. votes[a] = {}
    BY <2>4 DEF Init
  <2>6. VotedFor(a, b, v)
    BY <2>1, <2>3
  <2> QED
    BY <2>5, <2>6 DEF VotedFor
<1> QED
  BY <1>1 DEF chosen

LEMMA Step ==
  ASSUME Inv, Consistency, Consistency', [Next]_<<votes, maxBal>>
  PROVE  [C!Next]_chosen
<1>1. CASE <<votes, maxBal>>' = <<votes, maxBal>>
  <2>1. votes' = votes
    BY <1>1
  <2>2. chosen' = chosen
    BY <2>1 DEF chosen, ChosenAt, VotedFor
  <2> QED
    BY <2>2 DEF C!Next
<1>2. CASE Next
  <2>tok. TypeOK
    BY DEF Inv
  <2>1. chosen \subseteq chosen'
    <3>1. \A a \in Acceptor : votes[a] \subseteq votes'[a]
      BY VotesGrow, <2>tok, <1>2
    <3>2. \A b \in Ballot, v \in Value : ChosenAt(b, v) => ChosenAt(b, v)'
      <4> TAKE b \in Ballot, v \in Value
      <4> SUFFICES ASSUME ChosenAt(b, v) PROVE ChosenAt(b, v)'
        OBVIOUS
      <4>1. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
        BY DEF ChosenAt
      <4>2. \A a \in Q : VotedFor(a, b, v)'
        <5> TAKE a \in Q
        <5>1. a \in Acceptor
          BY <4>1, QuorumAssumption
        <5>2. VotedFor(a, b, v)
          BY <4>1
        <5>3. votes[a] \subseteq votes'[a]
          BY <3>1, <5>1
        <5> QED
          BY <5>2, <5>3 DEF VotedFor
      <4> QED
        BY <4>1, <4>2 DEF ChosenAt
    <3> QED
      BY <3>2 DEF chosen
  <2> QED
    <3>1. CASE chosen = {}
      <4>1. CASE chosen' = {}
        <5>1. chosen' = chosen
          BY <3>1, <4>1
        <5> QED
          BY <5>1 DEF C!Next
      <4>2. CASE chosen' # {}
        <5>1. PICK v \in Value : chosen' = {v}
          BY <4>2 DEF Consistency
        <5> QED
          BY <3>1, <5>1 DEF C!Next
      <4> QED
        BY <4>1, <4>2
    <3>2. CASE \E w \in Value : chosen = {w}
      <4>1. PICK w \in Value : chosen = {w}
        BY <3>2
      <4>2. w \in chosen'
        BY <4>1, <2>1
      <4>3. chosen' # {}
        BY <4>2
      <4>4. PICK v \in Value : chosen' = {v}
        BY <4>3 DEF Consistency
      <4>5. chosen' = chosen
        BY <4>1, <4>2, <4>4
      <4> QED
        BY <4>5 DEF C!Next
    <3> QED
      BY <3>1, <3>2 DEF Consistency
<1> QED
  BY <1>1, <1>2

THEOREM Refinement == Spec => C!Spec
<1>1. Init => C!Init
  BY InitC
<1>3. Spec => []Inv
  BY Invariant
<1>4. Spec => []Consistency
  BY Consistent
<1> QED
  BY <1>1, Step, <1>3, <1>4, PTL DEF Spec, C!Spec
=============================================================================