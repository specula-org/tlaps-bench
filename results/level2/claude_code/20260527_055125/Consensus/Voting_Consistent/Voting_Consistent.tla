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
ChosenAt(b, v) == 
    \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Consistency == chosen = {} \/ \E v \in Value : chosen = {v}
---------------------------------------------------------------------------

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

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
LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
  BY QuorumAssumption

-----------------------------------------------------------------------------
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
      OBVIOUS
  <1>1. TypeOK
    BY DEF Init, TypeOK, Ballot
  <1>2. VotesSafe
    BY DEF Init, VotesSafe, VotedFor
  <1>3. OneValuePerBallot
    BY DEF Init, OneValuePerBallot, VotedFor
  <1> QED BY <1>1, <1>2, <1>3 DEF Inv

-----------------------------------------------------------------------------
LEMMA VotedForUnchanged ==
   ASSUME NEW a \in Acceptor, NEW a1 \in Acceptor, NEW b \in Ballot,
          NEW v \in Value, NEW vt,
          votes' = [votes EXCEPT ![a] = votes[a] \cup {vt}],
          TypeOK,
          a1 # a
   PROVE VotedFor(a1, b, v)' <=> VotedFor(a1, b, v)
  BY DEF VotedFor, TypeOK

-----------------------------------------------------------------------------
LEMMA DidNotVoteAtUnchanged ==
   ASSUME NEW a \in Acceptor, NEW a1 \in Acceptor, NEW b \in Ballot,
          NEW vt,
          votes' = [votes EXCEPT ![a] = votes[a] \cup {vt}],
          TypeOK,
          a1 # a
   PROVE DidNotVoteAt(a1, b)' <=> DidNotVoteAt(a1, b)
  BY DEF DidNotVoteAt, VotedFor, TypeOK

-----------------------------------------------------------------------------
LEMMA NextTypeOK ==
   ASSUME TypeOK, Next
   PROVE  TypeOK'
  <1> USE DEF TypeOK, Ballot
  <1>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot, IncreaseMaxBal(a, b)
        PROVE TypeOK'
    BY <1>1 DEF IncreaseMaxBal
  <1>2. ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value, VoteFor(a, b, v)
        PROVE TypeOK'
    <2>1. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]
      BY <1>2 DEF VoteFor
    <2>2. maxBal' \in [Acceptor -> Ballot \cup {-1}]
      BY <1>2 DEF VoteFor
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2 DEF Next

-----------------------------------------------------------------------------
LEMMA SafeAtStableIncreaseMaxBal ==
   ASSUME TypeOK, NEW a \in Acceptor, NEW bb \in Ballot, IncreaseMaxBal(a, bb),
          NEW b \in Ballot, NEW v \in Value, SafeAt(b, v)
   PROVE SafeAt(b, v)'
  <1> USE DEF IncreaseMaxBal, SafeAt, NoneOtherChoosableAt, CannotVoteAt,
              DidNotVoteAt, VotedFor, TypeOK, Ballot
  <1>1. votes' = votes
    OBVIOUS
  <1>2. \A aa \in Acceptor : maxBal'[aa] >= maxBal[aa]
    BY DEF Ballot
  <1>3. SUFFICES ASSUME NEW c \in 0..(b-1)
                 PROVE NoneOtherChoosableAt(c, v)'
    BY DEF SafeAt
  <1>4. NoneOtherChoosableAt(c, v)
    BY DEF SafeAt
  <1>5. PICK Q \in Quorum : \A aa \in Q : VotedFor(aa, c, v) \/ CannotVoteAt(aa, c)
    BY <1>4 DEF NoneOtherChoosableAt
  <1>6. \A aa \in Q : VotedFor(aa, c, v)' \/ CannotVoteAt(aa, c)'
    <2> SUFFICES ASSUME NEW aa \in Q
                 PROVE VotedFor(aa, c, v)' \/ CannotVoteAt(aa, c)'
        OBVIOUS
    <2>1. aa \in Acceptor
      BY QuorumAssumption
    <2>2. CASE VotedFor(aa, c, v)
      BY <2>2, <1>1
    <2>3. CASE CannotVoteAt(aa, c)
      <3>1. maxBal'[aa] > c
        BY <2>3, <2>1, <1>2, QuorumAssumption
      <3>2. \A vv \in Value : ~ VotedFor(aa, c, vv)'
        BY <2>3, <1>1
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>2, <2>3, <1>5
  <1> QED BY <1>6 DEF NoneOtherChoosableAt

-----------------------------------------------------------------------------
LEMMA SafeAtStableVoteFor ==
   ASSUME TypeOK, NEW a0 \in Acceptor, NEW b0 \in Ballot, NEW v0 \in Value,
          VoteFor(a0, b0, v0),
          NEW b \in Ballot, NEW v \in Value, SafeAt(b, v)
   PROVE SafeAt(b, v)'
  <1> USE DEF VoteFor, SafeAt, NoneOtherChoosableAt, CannotVoteAt,
              DidNotVoteAt, VotedFor, TypeOK, Ballot
  <1>1. \A aa \in Acceptor : maxBal'[aa] >= maxBal[aa]
    OBVIOUS
  <1>2. \A aa \in Acceptor, bb \in Ballot, vv \in Value :
           VotedFor(aa, bb, vv) => VotedFor(aa, bb, vv)'
    <2> SUFFICES ASSUME NEW aa \in Acceptor, NEW bb \in Ballot, NEW vv \in Value,
                        VotedFor(aa, bb, vv)
                 PROVE VotedFor(aa, bb, vv)'
        OBVIOUS
    <2>1. CASE aa = a0
      <3>1. votes'[aa] = votes[aa] \cup {<<b0, v0>>}
        BY <2>1
      <3> QED BY <3>1
    <2>2. CASE aa # a0
      <3>1. votes'[aa] = votes[aa]
        BY <2>2
      <3> QED BY <3>1
    <2> QED BY <2>1, <2>2
  <1>3. SUFFICES ASSUME NEW c \in 0..(b-1)
                 PROVE NoneOtherChoosableAt(c, v)'
    BY DEF SafeAt
  <1>4. NoneOtherChoosableAt(c, v)
    BY DEF SafeAt
  <1>5. PICK Q \in Quorum : \A aa \in Q : VotedFor(aa, c, v) \/ CannotVoteAt(aa, c)
    BY <1>4 DEF NoneOtherChoosableAt
  <1>6. \A aa \in Q : VotedFor(aa, c, v)' \/ CannotVoteAt(aa, c)'
    <2> SUFFICES ASSUME NEW aa \in Q
                 PROVE VotedFor(aa, c, v)' \/ CannotVoteAt(aa, c)'
        OBVIOUS
    <2>1. aa \in Acceptor
      BY QuorumAssumption
    <2>2. CASE VotedFor(aa, c, v)
      BY <2>2, <1>2, <2>1
    <2>3. CASE CannotVoteAt(aa, c) /\ ~VotedFor(aa, c, v)
      <3>1. maxBal'[aa] > c
        BY <2>3, <2>1, <1>1
      <3>2. \A vv \in Value : ~ VotedFor(aa, c, vv)'
        <4> SUFFICES ASSUME NEW vv \in Value, VotedFor(aa, c, vv)'
                     PROVE FALSE
            OBVIOUS
        <4>1. CASE aa = a0
          <5>1. votes'[aa] = votes[aa] \cup {<<b0, v0>>}
            BY <4>1
          <5>2. <<c, vv>> \in votes[aa] \cup {<<b0, v0>>}
            BY <5>1
          <5>3. CASE <<c, vv>> \in votes[aa]
            BY <5>3, <2>3
          <5>4. CASE <<c, vv>> = <<b0, v0>>
            <6>1. c = b0
              BY <5>4
            <6>2. maxBal[a0] <= b0
              OBVIOUS
            <6>3. maxBal[aa] <= c
              BY <6>1, <6>2, <4>1
            <6> QED BY <6>3, <2>3, <2>1
          <5> QED BY <5>2, <5>3, <5>4
        <4>2. CASE aa # a0
          <5>0. aa \in Acceptor
            BY <2>1
          <5>1. votes'[aa] = votes[aa]
            BY <4>2, <5>0
          <5> QED BY <5>1, <2>3
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>2, <2>3, <1>5
  <1> QED BY <1>6 DEF NoneOtherChoosableAt

-----------------------------------------------------------------------------
LEMMA SafeAtStable ==
   ASSUME TypeOK, Next, NEW b \in Ballot, NEW v \in Value, SafeAt(b, v)
   PROVE SafeAt(b, v)'
  <1>1. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, IncreaseMaxBal(a, bb)
        PROVE SafeAt(b, v)'
    BY <1>1, SafeAtStableIncreaseMaxBal
  <1>2. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, NEW vv \in Value, VoteFor(a, bb, vv)
        PROVE SafeAt(b, v)'
    BY <1>2, SafeAtStableVoteFor
  <1> QED BY <1>1, <1>2 DEF Next

-----------------------------------------------------------------------------
LEMMA ShowsSafetyLemma ==
   ASSUME TypeOK, VotesSafe, OneValuePerBallot,
          NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
          ShowsSafeAt(Q, b, v)
   PROVE SafeAt(b, v)
  <1> USE DEF SafeAt, ShowsSafeAt, NoneOtherChoosableAt, CannotVoteAt,
              VotesSafe, OneValuePerBallot, DidNotVoteAt, VotedFor,
              TypeOK, Ballot
  <1>1. PICK c \in -1..(b-1) :
          /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
          /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
    OBVIOUS
  <1>2. \A a \in Q : maxBal[a] >= b
    OBVIOUS
  <1>3. SUFFICES ASSUME NEW e \in 0..(b-1)
                 PROVE NoneOtherChoosableAt(e, v)
    BY DEF SafeAt
  <1>4. CASE e > c
    <2>1. e \in (c+1)..(b-1)
      BY <1>4, <1>1
    <2>2. \A a \in Q : DidNotVoteAt(a, e)
      BY <2>1, <1>1
    <2>3. \A a \in Q : VotedFor(a, e, v) \/ CannotVoteAt(a, e)
      <3> SUFFICES ASSUME NEW a \in Q
                   PROVE VotedFor(a, e, v) \/ CannotVoteAt(a, e)
          OBVIOUS
      <3>1. a \in Acceptor
        BY QuorumAssumption
      <3>2. maxBal[a] \in Ballot \cup {-1}
        BY <3>1
      <3>3. maxBal[a] >= b
        BY <1>2
      <3>4. e < b
        OBVIOUS
      <3>5. maxBal[a] > e
        BY <3>2, <3>3, <3>4 DEF Ballot
      <3>6. DidNotVoteAt(a, e)
        BY <2>2
      <3> QED BY <3>5, <3>6 DEF CannotVoteAt
    <2> QED BY <2>3 DEF NoneOtherChoosableAt
  <1>5. CASE e <= c
    <2>1. c # -1
      BY <1>5
    <2>2. PICK a0 \in Q : VotedFor(a0, c, v)
      BY <1>1, <2>1
    <2>3. a0 \in Acceptor
      BY QuorumAssumption
    <2>4. c \in Ballot
      BY <2>1
    <2>5. SafeAt(c, v)
      BY <2>2, <2>3, <2>4 DEF VotesSafe, VotedFor
    <2>6. CASE e < c
      <3>1. e \in 0..(c-1)
        BY <2>6, <1>5, <2>4
      <3> QED BY <2>5, <3>1 DEF SafeAt
    <2>7. CASE e = c
      <3> SUFFICES NoneOtherChoosableAt(c, v)
          BY <2>7
      <3>1. \A a \in Q : VotedFor(a, c, v) \/ CannotVoteAt(a, c)
        <4> SUFFICES ASSUME NEW a \in Q
                     PROVE VotedFor(a, c, v) \/ CannotVoteAt(a, c)
            OBVIOUS
        <4>1. a \in Acceptor
          BY QuorumAssumption
        <4>2. maxBal[a] \in Ballot \cup {-1}
          BY <4>1
        <4>3. maxBal[a] >= b
          BY <1>2
        <4>4. c < b
          BY <2>4
        <4>5. maxBal[a] > c
          BY <2>4, <4>2, <4>3, <4>4 DEF Ballot
        <4>6. CASE VotedFor(a, c, v)
          BY <4>6
        <4>7. CASE ~VotedFor(a, c, v)
          <5>1. \A vv \in Value : ~VotedFor(a, c, vv)
            <6> SUFFICES ASSUME NEW vv \in Value, VotedFor(a, c, vv)
                         PROVE FALSE
                OBVIOUS
            <6>1. vv = v
              BY <2>2, <2>3, <4>1, <2>4 DEF OneValuePerBallot
            <6> QED BY <6>1, <4>7
          <5>2. DidNotVoteAt(a, c)
            BY <5>1 DEF DidNotVoteAt
          <5> QED BY <4>5, <5>2 DEF CannotVoteAt
        <4> QED BY <4>6, <4>7
      <3> QED BY <3>1 DEF NoneOtherChoosableAt
    <2> QED BY <2>6, <2>7, <1>5
  <1> QED BY <1>4, <1>5, <1>1 DEF Ballot

-----------------------------------------------------------------------------
LEMMA NextOneValuePerBallot ==
   ASSUME TypeOK, VotesSafe, OneValuePerBallot, Next
   PROVE OneValuePerBallot'
  <1> USE DEF OneValuePerBallot, VotedFor, TypeOK, Ballot
  <1>1. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, IncreaseMaxBal(a, bb)
        PROVE OneValuePerBallot'
    BY <1>1 DEF IncreaseMaxBal
  <1>2. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, NEW vv \in Value, VoteFor(a, bb, vv)
        PROVE OneValuePerBallot'
    <2> SUFFICES ASSUME NEW a1 \in Acceptor, NEW a2 \in Acceptor,
                        NEW b \in Ballot, NEW v1 \in Value, NEW v2 \in Value,
                        VotedFor(a1, b, v1)', VotedFor(a2, b, v2)'
                 PROVE v1 = v2
        OBVIOUS
    <2>1. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<bb, vv>>}]
      BY <1>2 DEF VoteFor
    <2>2. CASE a1 = a /\ a2 = a
      <3>1. votes'[a] = votes[a] \cup {<<bb, vv>>}
        BY <2>1
      <3>2. <<b, v1>> \in votes[a] \cup {<<bb, vv>>}
        BY <3>1, <2>2
      <3>3. <<b, v2>> \in votes[a] \cup {<<bb, vv>>}
        BY <3>1, <2>2
      <3>4. CASE <<b, v1>> \in votes[a] /\ <<b, v2>> \in votes[a]
        BY <3>4, <2>2
      <3>5. CASE <<b, v1>> = <<bb, vv>> /\ <<b, v2>> = <<bb, vv>>
        BY <3>5
      <3>6. CASE <<b, v1>> \in votes[a] /\ <<b, v2>> = <<bb, vv>>
        <4>1. \A vt \in votes[a] : vt[1] # bb
          BY <1>2 DEF VoteFor
        <4>2. b = bb
          BY <3>6
        <4>3. FALSE
          BY <3>6, <4>1, <4>2
        <4> QED BY <4>3
      <3>7. CASE <<b, v1>> = <<bb, vv>> /\ <<b, v2>> \in votes[a]
        <4>1. \A vt \in votes[a] : vt[1] # bb
          BY <1>2 DEF VoteFor
        <4>2. b = bb
          BY <3>7
        <4>3. FALSE
          BY <3>7, <4>1, <4>2
        <4> QED BY <4>3
      <3> QED BY <3>2, <3>3, <3>4, <3>5, <3>6, <3>7
    <2>3. CASE a1 = a /\ a2 # a
      <3>1. votes'[a1] = votes[a] \cup {<<bb, vv>>}
        BY <2>1, <2>3
      <3>2. votes'[a2] = votes[a2]
        BY <2>1, <2>3
      <3>3. <<b, v1>> \in votes[a] \cup {<<bb, vv>>}
        BY <3>1
      <3>4. <<b, v2>> \in votes[a2]
        BY <3>2
      <3>5. CASE <<b, v1>> \in votes[a]
        BY <3>5, <3>4, <2>3
      <3>6. CASE <<b, v1>> = <<bb, vv>>
        <4>1. b = bb /\ v1 = vv
          BY <3>6
        <4>2. \A c \in Acceptor \ {a} : \A vt \in votes[c] : (vt[1] = bb) => (vt[2] = vv)
          BY <1>2 DEF VoteFor
        <4>3. a2 \in Acceptor \ {a}
          BY <2>3
        <4>4. <<b, v2>>[1] = bb
          BY <4>1
        <4>5. <<b, v2>>[2] = vv
          BY <4>2, <4>3, <4>4, <3>4
        <4> QED BY <4>1, <4>5
      <3> QED BY <3>3, <3>5, <3>6
    <2>4. CASE a1 # a /\ a2 = a
      <3>1. votes'[a1] = votes[a1]
        BY <2>1, <2>4
      <3>2. votes'[a2] = votes[a] \cup {<<bb, vv>>}
        BY <2>1, <2>4
      <3>3. <<b, v1>> \in votes[a1]
        BY <3>1
      <3>4. <<b, v2>> \in votes[a] \cup {<<bb, vv>>}
        BY <3>2
      <3>5. CASE <<b, v2>> \in votes[a]
        BY <3>5, <3>3, <2>4
      <3>6. CASE <<b, v2>> = <<bb, vv>>
        <4>1. b = bb /\ v2 = vv
          BY <3>6
        <4>2. \A c \in Acceptor \ {a} : \A vt \in votes[c] : (vt[1] = bb) => (vt[2] = vv)
          BY <1>2 DEF VoteFor
        <4>3. a1 \in Acceptor \ {a}
          BY <2>4
        <4>4. <<b, v1>>[1] = bb
          BY <4>1
        <4>5. <<b, v1>>[2] = vv
          BY <4>2, <4>3, <4>4, <3>3
        <4> QED BY <4>1, <4>5
      <3> QED BY <3>4, <3>5, <3>6
    <2>5. CASE a1 # a /\ a2 # a
      <3>1. votes'[a1] = votes[a1]
        BY <2>1, <2>5
      <3>2. votes'[a2] = votes[a2]
        BY <2>1, <2>5
      <3>3. <<b, v1>> \in votes[a1]
        BY <3>1
      <3>4. <<b, v2>> \in votes[a2]
        BY <3>2
      <3> QED BY <3>3, <3>4
    <2> QED BY <2>2, <2>3, <2>4, <2>5
  <1> QED BY <1>1, <1>2 DEF Next

-----------------------------------------------------------------------------
LEMMA NextVotesSafe ==
   ASSUME TypeOK, VotesSafe, OneValuePerBallot, Next
   PROVE VotesSafe'
  <1> USE DEF VotesSafe, VotedFor, TypeOK, Ballot
  <1>1. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, IncreaseMaxBal(a, bb)
        PROVE VotesSafe'
    <2> SUFFICES ASSUME NEW aa \in Acceptor, NEW b \in Ballot, NEW v \in Value,
                        VotedFor(aa, b, v)'
                 PROVE SafeAt(b, v)'
        BY DEF VotesSafe
    <2>1. votes' = votes
      BY <1>1 DEF IncreaseMaxBal
    <2>2. VotedFor(aa, b, v)
      BY <2>1
    <2>3. SafeAt(b, v)
      BY <2>2 DEF VotesSafe
    <2>4. TypeOK
      OBVIOUS
    <2> QED BY <2>3, <2>4, <1>1, SafeAtStable DEF Next
  <1>2. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, NEW vv \in Value, VoteFor(a, bb, vv)
        PROVE VotesSafe'
    <2> SUFFICES ASSUME NEW aa \in Acceptor, NEW b \in Ballot, NEW v \in Value,
                        VotedFor(aa, b, v)'
                 PROVE SafeAt(b, v)'
        BY DEF VotesSafe
    <2>1. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<bb, vv>>}]
      BY <1>2 DEF VoteFor
    <2>2. CASE VotedFor(aa, b, v)
      <3>1. SafeAt(b, v)
        BY <2>2 DEF VotesSafe
      <3>2. TypeOK
        OBVIOUS
      <3> QED BY <3>1, <3>2, <1>2, SafeAtStable DEF Next
    <2>3. CASE ~VotedFor(aa, b, v)
      <3>1. CASE aa = a
        <4>1. votes'[aa] = votes[a] \cup {<<bb, vv>>}
          BY <2>1, <3>1
        <4>2. <<b, v>> \in votes'[aa]
          OBVIOUS
        <4>3. <<b, v>> \in votes[a] \cup {<<bb, vv>>}
          BY <4>1, <4>2
        <4>4. <<b, v>> = <<bb, vv>>
          BY <4>3, <2>3, <3>1
        <4>5. b = bb /\ v = vv
          BY <4>4
        <4>6. \E Q \in Quorum : ShowsSafeAt(Q, bb, vv)
          BY <1>2 DEF VoteFor
        <4>7. PICK Q \in Quorum : ShowsSafeAt(Q, bb, vv)
          BY <4>6
        <4>8. SafeAt(bb, vv)
          BY <4>7, ShowsSafetyLemma
        <4>9. SafeAt(b, v)
          BY <4>5, <4>8
        <4>10. TypeOK
          OBVIOUS
        <4> QED BY <4>9, <4>10, <1>2, SafeAtStable DEF Next
      <3>2. CASE aa # a
        <4>1. votes'[aa] = votes[aa]
          BY <2>1, <3>2
        <4>2. VotedFor(aa, b, v)
          BY <4>1 DEF VotedFor
        <4> QED BY <4>2, <2>3
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>2, <2>3
  <1> QED BY <1>1, <1>2 DEF Next

-----------------------------------------------------------------------------
LEMMA NextInv ==
   ASSUME Inv, Next
   PROVE Inv'
  <1>1. TypeOK
    BY DEF Inv
  <1>2. VotesSafe
    BY DEF Inv
  <1>3. OneValuePerBallot
    BY DEF Inv
  <1>4. TypeOK'
    BY <1>1, NextTypeOK
  <1>5. VotesSafe'
    BY <1>1, <1>2, <1>3, NextVotesSafe
  <1>6. OneValuePerBallot'
    BY <1>1, <1>2, <1>3, NextOneValuePerBallot
  <1> QED BY <1>4, <1>5, <1>6 DEF Inv

-----------------------------------------------------------------------------
LEMMA StutterInv ==
   ASSUME Inv, UNCHANGED <<votes, maxBal>>
   PROVE Inv'
  <1> USE DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, SafeAt,
              NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt, VotedFor
  <1> QED OBVIOUS

-----------------------------------------------------------------------------
LEMMA Invariance == Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_<<votes, maxBal>> => Inv'
    <2> SUFFICES ASSUME Inv, [Next]_<<votes, maxBal>>
                 PROVE Inv'
        OBVIOUS
    <2>1. CASE Next
      BY <2>1, NextInv
    <2>2. CASE UNCHANGED <<votes, maxBal>>
      BY <2>2, StutterInv
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
LEMMA TwoChosenEqual ==
   ASSUME Inv,
          NEW v1 \in Value, NEW b1 \in Ballot, ChosenAt(b1, v1),
          NEW v2 \in Value, NEW b2 \in Ballot, ChosenAt(b2, v2)
   PROVE v1 = v2
  <1> USE DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, ChosenAt,
              VotedFor, SafeAt, NoneOtherChoosableAt,
              CannotVoteAt, DidNotVoteAt, Ballot
  <1>1. PICK Q1 \in Quorum : \A a \in Q1 : VotedFor(a, b1, v1)
    OBVIOUS
  <1>2. PICK Q2 \in Quorum : \A a \in Q2 : VotedFor(a, b2, v2)
    OBVIOUS
  <1>3. CASE b1 = b2
    <2>1. Q1 \cap Q2 # {}
      BY QuorumAssumption
    <2>2. PICK a \in Q1 \cap Q2 : TRUE
      BY <2>1
    <2>3. a \in Acceptor
      BY <2>2, QuorumAssumption
    <2>4. VotedFor(a, b1, v1)
      BY <2>2, <1>1
    <2>5. VotedFor(a, b2, v2)
      BY <2>2, <1>2
    <2>6. VotedFor(a, b1, v2)
      BY <2>5, <1>3
    <2> QED BY <2>3, <2>4, <2>6
  <1>4. CASE b1 < b2
    <2>1. SafeAt(b2, v2)
      <3>1. Q2 # {}
        BY QuorumNonEmpty
      <3>2. PICK aa \in Q2 : TRUE
        BY <3>1
      <3>3. aa \in Acceptor
        BY <3>2, QuorumAssumption
      <3>4. VotedFor(aa, b2, v2)
        BY <3>2, <1>2
      <3> QED BY <3>3, <3>4
    <2>2. b1 \in 0..(b2-1)
      BY <1>4 DEF Ballot
    <2>3. NoneOtherChoosableAt(b1, v2)
      BY <2>1, <2>2
    <2>4. PICK Q3 \in Quorum : \A a \in Q3 : VotedFor(a, b1, v2) \/ CannotVoteAt(a, b1)
      BY <2>3
    <2>5. Q1 \cap Q3 # {}
      BY QuorumAssumption
    <2>6. PICK a \in Q1 \cap Q3 : TRUE
      BY <2>5
    <2>7. a \in Acceptor
      BY <2>6, QuorumAssumption
    <2>8. VotedFor(a, b1, v1)
      BY <2>6, <1>1
    <2>9. VotedFor(a, b1, v2) \/ CannotVoteAt(a, b1)
      BY <2>6, <2>4
    <2>10. CASE VotedFor(a, b1, v2)
      BY <2>7, <2>8, <2>10
    <2>11. CASE CannotVoteAt(a, b1)
      BY <2>11, <2>8
    <2> QED BY <2>9, <2>10, <2>11
  <1>5. CASE b2 < b1
    <2>1. SafeAt(b1, v1)
      <3>1. Q1 # {}
        BY QuorumNonEmpty
      <3>2. PICK aa \in Q1 : TRUE
        BY <3>1
      <3>3. aa \in Acceptor
        BY <3>2, QuorumAssumption
      <3>4. VotedFor(aa, b1, v1)
        BY <3>2, <1>1
      <3> QED BY <3>3, <3>4
    <2>2. b2 \in 0..(b1-1)
      BY <1>5 DEF Ballot
    <2>3. NoneOtherChoosableAt(b2, v1)
      BY <2>1, <2>2
    <2>4. PICK Q3 \in Quorum : \A a \in Q3 : VotedFor(a, b2, v1) \/ CannotVoteAt(a, b2)
      BY <2>3
    <2>5. Q2 \cap Q3 # {}
      BY QuorumAssumption
    <2>6. PICK a \in Q2 \cap Q3 : TRUE
      BY <2>5
    <2>7. a \in Acceptor
      BY <2>6, QuorumAssumption
    <2>8. VotedFor(a, b2, v2)
      BY <2>6, <1>2
    <2>9. VotedFor(a, b2, v1) \/ CannotVoteAt(a, b2)
      BY <2>6, <2>4
    <2>10. CASE VotedFor(a, b2, v1)
      BY <2>7, <2>8, <2>10
    <2>11. CASE CannotVoteAt(a, b2)
      BY <2>11, <2>8
    <2> QED BY <2>9, <2>10, <2>11
  <1> QED BY <1>3, <1>4, <1>5 DEF Ballot

-----------------------------------------------------------------------------
LEMMA InvImpliesConsistency ==
   ASSUME Inv
   PROVE Consistency
  <1> USE DEF Consistency, chosen, ChosenAt
  <1>1. CASE chosen = {}
    BY <1>1
  <1>2. CASE chosen # {}
    <2>1. PICK v0 \in chosen : TRUE
      BY <1>2
    <2>2. v0 \in Value
      BY <2>1
    <2>3. \A v \in chosen : v = v0
      <3> SUFFICES ASSUME NEW v \in chosen PROVE v = v0
          OBVIOUS
      <3>1. PICK b_v \in Ballot : ChosenAt(b_v, v)
        BY DEF chosen
      <3>2. PICK b_v0 \in Ballot : ChosenAt(b_v0, v0)
        BY <2>1 DEF chosen
      <3>3. v \in Value
        OBVIOUS
      <3> QED BY <2>2, <3>1, <3>2, <3>3, TwoChosenEqual
    <2>4. chosen = {v0}
      BY <2>3, <2>1
    <2> QED BY <2>2, <2>4
  <1> QED BY <1>1, <1>2

-----------------------------------------------------------------------------
THEOREM Consistent == Spec => []Consistency
<1>1. Spec => []Inv
  BY Invariance
<1>2. []Inv => []Consistency
  <2>1. Inv => Consistency
    BY InvImpliesConsistency
  <2> QED BY <2>1, PTL
<1> QED BY <1>1, <1>2, PTL
----------------------------------------------------------------------------

=============================================================================