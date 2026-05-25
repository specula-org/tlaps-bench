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
\* ===================  Helper lemmas for the inductive proof  ===============

LEMMA VotesMonotone ==
  ASSUME TypeOK, Next, NEW x \in Acceptor
  PROVE  votes[x] \subseteq votes'[x]
<1> USE DEF Ballot
<1>1. PICK a \in Acceptor, bb \in Ballot :
        \/ IncreaseMaxBal(a, bb)
        \/ \E w \in Value : VoteFor(a, bb, w)
  BY DEF Next
<1>2. CASE IncreaseMaxBal(a, bb)
  <2>1. votes' = votes  BY <1>2 DEF IncreaseMaxBal
  <2>2. QED BY <2>1
<1>3. CASE \E w \in Value : VoteFor(a, bb, w)
  <2>1. PICK w \in Value : VoteFor(a, bb, w)  BY <1>3
  <2>2. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<bb, w>>}]  BY <2>1 DEF VoteFor
  <2>3. CASE x = a
    <3>1. votes'[x] = votes[a] \cup {<<bb, w>>}  BY <2>2, <2>3 DEF TypeOK
    <3>2. QED BY <3>1, <2>3
  <2>4. CASE x # a
    <3>1. votes'[x] = votes[x]  BY <2>2, <2>4 DEF TypeOK
    <3>2. QED BY <3>1
  <2>5. QED BY <2>3, <2>4
<1>4. QED BY <1>1, <1>2, <1>3

LEMMA MaxBalMonotone ==
  ASSUME TypeOK, Next, NEW x \in Acceptor
  PROVE  maxBal[x] <= maxBal'[x]
<1> USE DEF Ballot
<1>0. maxBal[x] \in Int  BY DEF TypeOK
<1>1. PICK a \in Acceptor, bb \in Ballot :
        \/ IncreaseMaxBal(a, bb)
        \/ \E w \in Value : VoteFor(a, bb, w)
  BY DEF Next
<1>2. CASE IncreaseMaxBal(a, bb)
  <2>1. maxBal' = [maxBal EXCEPT ![a] = bb] /\ bb > maxBal[a]  BY <1>2 DEF IncreaseMaxBal
  <2>2. maxBal[a] \in Int /\ bb \in Int  BY DEF TypeOK
  <2>3. CASE x = a
    <3>1. maxBal'[x] = bb  BY <2>1, <2>3 DEF TypeOK
    <3>2. QED BY <3>1, <2>1, <2>2, <2>3
  <2>4. CASE x # a
    <3>1. maxBal'[x] = maxBal[x]  BY <2>1, <2>4 DEF TypeOK
    <3>2. QED BY <3>1, <1>0
  <2>5. QED BY <2>3, <2>4
<1>3. CASE \E w \in Value : VoteFor(a, bb, w)
  <2>1. PICK w \in Value : VoteFor(a, bb, w)  BY <1>3
  <2>2. maxBal' = [maxBal EXCEPT ![a] = bb] /\ maxBal[a] <= bb  BY <2>1 DEF VoteFor
  <2>3. maxBal[a] \in Int /\ bb \in Int  BY DEF TypeOK
  <2>4. CASE x = a
    <3>1. maxBal'[x] = bb  BY <2>2, <2>4 DEF TypeOK
    <3>2. QED BY <3>1, <2>2, <2>3, <2>4
  <2>5. CASE x # a
    <3>1. maxBal'[x] = maxBal[x]  BY <2>2, <2>5 DEF TypeOK
    <3>2. QED BY <3>1, <1>0
  <2>6. QED BY <2>4, <2>5
<1>4. QED BY <1>1, <1>2, <1>3

LEMMA VoteStep ==
  ASSUME TypeOK, Next, NEW x \in Acceptor, NEW cc \in Ballot, NEW vv \in Value,
         VotedFor(x, cc, vv)', ~ VotedFor(x, cc, vv)
  PROVE  maxBal[x] <= cc
<1> USE DEF Ballot
<1>1. PICK a \in Acceptor, bb \in Ballot :
        \/ IncreaseMaxBal(a, bb)
        \/ \E w \in Value : VoteFor(a, bb, w)
  BY DEF Next
<1>2. CASE IncreaseMaxBal(a, bb)
  <2>1. votes' = votes  BY <1>2 DEF IncreaseMaxBal
  <2>2. VotedFor(x, cc, vv)  BY <2>1 DEF VotedFor
  <2>3. QED BY <2>2
<1>3. CASE \E w \in Value : VoteFor(a, bb, w)
  <2>1. PICK w \in Value : VoteFor(a, bb, w)  BY <1>3
  <2>2. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<bb, w>>}] /\ maxBal[a] <= bb
    BY <2>1 DEF VoteFor
  <2>3. CASE x # a
    <3>1. votes'[x] = votes[x]  BY <2>2, <2>3 DEF TypeOK
    <3>2. VotedFor(x, cc, vv)  BY <3>1 DEF VotedFor
    <3>3. QED BY <3>2
  <2>4. CASE x = a
    <3>1. votes'[x] = votes[x] \cup {<<bb, w>>}  BY <2>2, <2>4 DEF TypeOK
    <3>2. <<cc, vv>> \in votes[x] \cup {<<bb, w>>}  BY <3>1 DEF VotedFor
    <3>3. <<cc, vv>> \notin votes[x]  BY DEF VotedFor
    <3>4. <<cc, vv>> = <<bb, w>>  BY <3>2, <3>3
    <3>5. cc = bb  BY <3>4
    <3>6. QED BY <2>2, <2>4, <3>5
  <2>5. QED BY <2>3, <2>4
<1>4. QED BY <1>1, <1>2, <1>3

LEMMA CannotVoteStable ==
  ASSUME TypeOK, TypeOK', Next, NEW x \in Acceptor, NEW cc \in Ballot, CannotVoteAt(x, cc)
  PROVE  CannotVoteAt(x, cc)'
<1> USE DEF Ballot
<1>1. maxBal[x] > cc /\ DidNotVoteAt(x, cc)  BY DEF CannotVoteAt
<1>2. maxBal[x] <= maxBal'[x]  BY MaxBalMonotone
<1>3. maxBal[x] \in Int /\ maxBal'[x] \in Int /\ cc \in Int  BY DEF TypeOK
<1>4. maxBal'[x] > cc  BY <1>1, <1>2, <1>3
<1>5. DidNotVoteAt(x, cc)'
  <2> SUFFICES ASSUME NEW vv \in Value, VotedFor(x, cc, vv)'
               PROVE  FALSE
    BY DEF DidNotVoteAt
  <2>1. ~ VotedFor(x, cc, vv)  BY <1>1 DEF DidNotVoteAt
  <2>2. maxBal[x] <= cc  BY VoteStep, <2>1
  <2>3. QED BY <1>1, <2>2, <1>3
<1>6. QED BY <1>4, <1>5 DEF CannotVoteAt

LEMMA ShowsSafety ==
  ASSUME TypeOK, VotesSafe, OneValuePerBallot,
         NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
         ShowsSafeAt(Q, b, v)
  PROVE  SafeAt(b, v)
<1> USE DEF Ballot
<1>0. Q \subseteq Acceptor  BY QuorumAssumption
<1>1. PICK c \in -1..(b-1) :
        /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
        /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
  BY DEF ShowsSafeAt
<1>2. \A a \in Q : maxBal[a] \geq b  BY DEF ShowsSafeAt
<1> SUFFICES ASSUME NEW cc \in 0..(b-1)
             PROVE  NoneOtherChoosableAt(cc, v)
  BY DEF SafeAt
<1>3. CASE cc \in (c+1)..(b-1)
  <2>1. \A a \in Q : VotedFor(a, cc, v) \/ CannotVoteAt(a, cc)
    <3>1. SUFFICES ASSUME NEW a \in Q PROVE CannotVoteAt(a, cc)  OBVIOUS
    <3>2. a \in Acceptor  BY <1>0
    <3>3. DidNotVoteAt(a, cc)  BY <1>1, <1>3
    <3>4. maxBal[a] \geq b  BY <1>2
    <3>5. maxBal[a] \in Int  BY <3>2 DEF TypeOK
    <3>6. maxBal[a] > cc  BY <3>4, <3>5, <1>3
    <3>7. QED BY <3>3, <3>6 DEF CannotVoteAt
  <2>2. QED BY <2>1 DEF NoneOtherChoosableAt
<1>4. CASE cc \in 0..c
  <2>1. c # -1  BY <1>4
  <2>2. c \in 0..(b-1)  BY <1>1, <1>4
  <2>3. c \in Ballot  BY <2>2
  <2>4. PICK a0 \in Q : VotedFor(a0, c, v)  BY <1>1, <2>1
  <2>5. a0 \in Acceptor  BY <1>0, <2>4
  <2>6. SafeAt(c, v)  BY <2>4, <2>5, <2>3 DEF VotesSafe
  <2>7. CASE cc = c
    <3>1. SUFFICES NoneOtherChoosableAt(c, v)  BY <2>7
    <3>2. SUFFICES ASSUME NEW a \in Q
                   PROVE  VotedFor(a, c, v) \/ CannotVoteAt(a, c)
      BY DEF NoneOtherChoosableAt
    <3>3. a \in Acceptor  BY <1>0
    <3>4. maxBal[a] \geq b  BY <1>2
    <3>5. maxBal[a] \in Int  BY <3>3 DEF TypeOK
    <3>6. maxBal[a] > c  BY <3>4, <3>5, <2>2
    <3>7. CASE \E w \in Value : VotedFor(a, c, w)
      <4>1. PICK w \in Value : VotedFor(a, c, w)  BY <3>7
      <4>2. w = v  BY <4>1, <2>4, <2>5, <3>3, <2>3 DEF OneValuePerBallot
      <4>3. QED BY <4>1, <4>2
    <3>8. CASE ~ \E w \in Value : VotedFor(a, c, w)
      <4>1. DidNotVoteAt(a, c)  BY <3>8 DEF DidNotVoteAt
      <4>2. CannotVoteAt(a, c)  BY <4>1, <3>6 DEF CannotVoteAt
      <4>3. QED BY <4>2
    <3>9. QED BY <3>7, <3>8
  <2>8. CASE cc \in 0..(c-1)
    BY <2>6, <2>8 DEF SafeAt
  <2>9. QED BY <2>7, <2>8, <1>4, <2>2
<1>5. QED BY <1>1, <1>3, <1>4

LEMMA SafeAtStable ==
  ASSUME TypeOK, TypeOK', Next,
         NEW b \in Ballot, NEW v \in Value, SafeAt(b, v)
  PROVE  SafeAt(b, v)'
<1> USE DEF Ballot
<1> SUFFICES ASSUME NEW cc \in 0..(b-1)
             PROVE  NoneOtherChoosableAt(cc, v)'
  BY DEF SafeAt
<1>0. cc \in Ballot  BY DEF Ballot
<1>1. PICK Q \in Quorum : \A aa \in Q : VotedFor(aa, cc, v) \/ CannotVoteAt(aa, cc)
  BY DEF SafeAt, NoneOtherChoosableAt
<1>2. Q \subseteq Acceptor  BY QuorumAssumption
<1> SUFFICES ASSUME NEW aa \in Q
             PROVE  (VotedFor(aa, cc, v) \/ CannotVoteAt(aa, cc))'
  BY DEF NoneOtherChoosableAt
<1>3. VotedFor(aa, cc, v) \/ CannotVoteAt(aa, cc)  BY <1>1
<1>4. aa \in Acceptor  BY <1>2
<1>5. CASE VotedFor(aa, cc, v)
  <2>1. votes[aa] \subseteq votes'[aa]  BY VotesMonotone, <1>4
  <2>2. VotedFor(aa, cc, v)'  BY <2>1, <1>5 DEF VotedFor
  <2>3. QED BY <2>2
<1>6. CASE CannotVoteAt(aa, cc)
  <2>1. CannotVoteAt(aa, cc)'  BY CannotVoteStable, <1>6, <1>4, <1>0
  <2>2. QED BY <2>1
<1>7. QED BY <1>3, <1>5, <1>6

-----------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballot
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <2>1. TypeOK  BY DEF Init, TypeOK
  <2>2. VotesSafe  BY DEF Init, VotesSafe, VotedFor
  <2>3. OneValuePerBallot  BY DEF Init, OneValuePerBallot, VotedFor
  <2>4. QED BY <2>1, <2>2, <2>3 DEF Inv
<1>2. Inv /\ [Next]_<<votes, maxBal>> => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_<<votes, maxBal>> PROVE Inv'  OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE UNCHANGED <<votes, maxBal>>
    BY <2>1 DEF Inv, TypeOK, VotesSafe, SafeAt, NoneOtherChoosableAt,
               CannotVoteAt, DidNotVoteAt, VotedFor, OneValuePerBallot
  <2>2. CASE Next
    <3>0. PICK a \in Acceptor, bb \in Ballot :
            \/ IncreaseMaxBal(a, bb)
            \/ \E vv \in Value : VoteFor(a, bb, vv)
      BY <2>2 DEF Next
    <3>1. TypeOK'
      <4>1. CASE IncreaseMaxBal(a, bb)
        <5>1. votes' = votes /\ maxBal' = [maxBal EXCEPT ![a] = bb]
          BY <4>1 DEF IncreaseMaxBal
        <5>2. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]  BY <5>1 DEF TypeOK
        <5>3. maxBal' \in [Acceptor -> Ballot \cup {-1}]  BY <5>1 DEF TypeOK
        <5>4. QED BY <5>2, <5>3 DEF TypeOK
      <4>2. CASE \E vv \in Value : VoteFor(a, bb, vv)
        <5>1. PICK vv \in Value : VoteFor(a, bb, vv)  BY <4>2
        <5>2. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<bb, vv>>}]
              /\ maxBal' = [maxBal EXCEPT ![a] = bb]
          BY <5>1 DEF VoteFor
        <5>3. <<bb, vv>> \in Ballot \X Value  BY DEF Ballot
        <5>4. votes[a] \cup {<<bb, vv>>} \in SUBSET (Ballot \X Value)  BY <5>3 DEF TypeOK
        <5>5. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]  BY <5>2, <5>4 DEF TypeOK
        <5>6. maxBal' \in [Acceptor -> Ballot \cup {-1}]  BY <5>2 DEF TypeOK
        <5>7. QED BY <5>5, <5>6 DEF TypeOK
      <4>3. QED BY <3>0, <4>1, <4>2
    <3>2. OneValuePerBallot'
      <4> SUFFICES ASSUME NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW bal \in Ballot,
                          NEW v1 \in Value, NEW v2 \in Value,
                          VotedFor(a1, bal, v1)', VotedFor(a2, bal, v2)'
                   PROVE  v1 = v2
        BY DEF OneValuePerBallot
      <4>1. CASE IncreaseMaxBal(a, bb)
        <5>1. votes' = votes  BY <4>1 DEF IncreaseMaxBal
        <5>2. VotedFor(a1, bal, v1) /\ VotedFor(a2, bal, v2)  BY <5>1 DEF VotedFor
        <5>3. QED BY <5>2 DEF OneValuePerBallot
      <4>2. CASE \E vv \in Value : VoteFor(a, bb, vv)
        <5>1. PICK vv \in Value : VoteFor(a, bb, vv)  BY <4>2
        <5>2. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<bb, vv>>}]  BY <5>1 DEF VoteFor
        <5>3. /\ \A vt \in votes[a] : vt[1] # bb
              /\ \A cx \in Acceptor \ {a} : \A vt \in votes[cx] : (vt[1] = bb) => (vt[2] = vv)
          BY <5>1 DEF VoteFor
        <5>4. \A y \in Acceptor, u \in Value : VotedFor(y, bb, u)' => u = vv
          <6> SUFFICES ASSUME NEW y \in Acceptor, NEW u \in Value, VotedFor(y, bb, u)'
                       PROVE  u = vv
            OBVIOUS
          <6>0. <<bb, u>> \in votes'[y]  BY DEF VotedFor
          <6>1. CASE y = a
            <7>1. votes'[y] = votes[a] \cup {<<bb, vv>>}  BY <5>2, <6>1 DEF TypeOK
            <7>2. <<bb, u>> \in votes[a] \cup {<<bb, vv>>}  BY <6>0, <7>1
            <7>3. <<bb, u>> \notin votes[a]  BY <5>3
            <7>4. <<bb, u>> = <<bb, vv>>  BY <7>2, <7>3
            <7>5. QED BY <7>4
          <6>2. CASE y # a
            <7>1. votes'[y] = votes[y]  BY <5>2, <6>2 DEF TypeOK
            <7>2. <<bb, u>> \in votes[y]  BY <6>0, <7>1
            <7>3. y \in Acceptor \ {a}  BY <6>2
            <7>4. QED BY <7>2, <7>3, <5>3
          <6>3. QED BY <6>1, <6>2
        <5>5. CASE bal = bb
          <6>1. v1 = vv  BY <5>4, <5>5
          <6>2. v2 = vv  BY <5>4, <5>5
          <6>3. QED BY <6>1, <6>2
        <5>6. CASE bal # bb
          <6>1. VotedFor(a1, bal, v1)
            <7>1. <<bal, v1>> \in votes'[a1]  BY DEF VotedFor
            <7>2. votes'[a1] \subseteq votes[a1] \cup {<<bb, vv>>}  BY <5>2 DEF TypeOK
            <7>3. <<bal, v1>> \in votes[a1] \cup {<<bb, vv>>}  BY <7>1, <7>2
            <7>4. <<bal, v1>> # <<bb, vv>>  BY <5>6
            <7>5. <<bal, v1>> \in votes[a1]  BY <7>3, <7>4
            <7>6. QED BY <7>5 DEF VotedFor
          <6>2. VotedFor(a2, bal, v2)
            <7>1. <<bal, v2>> \in votes'[a2]  BY DEF VotedFor
            <7>2. votes'[a2] \subseteq votes[a2] \cup {<<bb, vv>>}  BY <5>2 DEF TypeOK
            <7>3. <<bal, v2>> \in votes[a2] \cup {<<bb, vv>>}  BY <7>1, <7>2
            <7>4. <<bal, v2>> # <<bb, vv>>  BY <5>6
            <7>5. <<bal, v2>> \in votes[a2]  BY <7>3, <7>4
            <7>6. QED BY <7>5 DEF VotedFor
          <6>3. QED BY <6>1, <6>2 DEF OneValuePerBallot
        <5>7. QED BY <5>5, <5>6
      <4>3. QED BY <3>0, <4>1, <4>2
    <3>3. VotesSafe'
      <4> SUFFICES ASSUME NEW a1 \in Acceptor, NEW bal \in Ballot, NEW v1 \in Value,
                          VotedFor(a1, bal, v1)'
                   PROVE  SafeAt(bal, v1)'
        BY DEF VotesSafe
      <4>1. CASE IncreaseMaxBal(a, bb)
        <5>1. votes' = votes  BY <4>1 DEF IncreaseMaxBal
        <5>2. VotedFor(a1, bal, v1)  BY <5>1 DEF VotedFor
        <5>3. SafeAt(bal, v1)  BY <5>2 DEF VotesSafe
        <5>4. QED BY <5>3, <3>1, <2>2, SafeAtStable
      <4>2. CASE \E vv \in Value : VoteFor(a, bb, vv)
        <5>1. PICK vv \in Value : VoteFor(a, bb, vv)  BY <4>2
        <5>2. CASE VotedFor(a1, bal, v1)
          <6>1. SafeAt(bal, v1)  BY <5>2 DEF VotesSafe
          <6>2. QED BY <6>1, <3>1, <2>2, SafeAtStable
        <5>3. CASE ~ VotedFor(a1, bal, v1)
          <6>1. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<bb, vv>>}]  BY <5>1 DEF VoteFor
          <6>2. a1 = a /\ bal = bb /\ v1 = vv
            <7>1. <<bal, v1>> \in votes'[a1]  BY DEF VotedFor
            <7>2. CASE a1 # a
              <8>1. votes'[a1] = votes[a1]  BY <6>1, <7>2 DEF TypeOK
              <8>2. VotedFor(a1, bal, v1)  BY <8>1, <7>1 DEF VotedFor
              <8>3. QED BY <8>2, <5>3
            <7>3. CASE a1 = a
              <8>1. votes'[a1] = votes[a1] \cup {<<bb, vv>>}  BY <6>1, <7>3 DEF TypeOK
              <8>2. <<bal, v1>> \notin votes[a1]  BY <5>3 DEF VotedFor
              <8>3. <<bal, v1>> = <<bb, vv>>  BY <7>1, <8>1, <8>2
              <8>4. QED BY <8>3, <7>3
            <7>4. QED BY <7>2, <7>3
          <6>3. PICK Q \in Quorum : ShowsSafeAt(Q, bb, vv)  BY <5>1 DEF VoteFor
          <6>4. SafeAt(bb, vv)  BY <6>3, ShowsSafety
          <6>5. SafeAt(bal, v1)  BY <6>4, <6>2
          <6>6. QED BY <6>5, <3>1, <2>2, SafeAtStable, <6>2
        <5>4. QED BY <5>2, <5>3
      <4>3. QED BY <3>0, <4>1, <4>2
    <3>4. QED BY <3>1, <3>2, <3>3 DEF Inv
  <2>3. QED BY <2>1, <2>2
<1>3. QED BY <1>1, <1>2, PTL DEF Spec
----------------------------------------------------------------------------
----------------------------------------------------------------------------
C == INSTANCE Consensus \* WITH chosen <- chosen

=============================================================================