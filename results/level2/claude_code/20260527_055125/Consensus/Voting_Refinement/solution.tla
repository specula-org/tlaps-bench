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

---------------------------------------------------------------------------

vars == <<votes, maxBal>>

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

ChosenSingleton == \A v0, w0 \in chosen : v0 = w0

-----------------------------------------------------------------------------

C == INSTANCE Consensus

-----------------------------------------------------------------------------

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
  BY QuorumAssumption

LEMMA InitTypeOK == Init => TypeOK
  BY DEF Init, TypeOK, Ballot

LEMMA InitVotesSafe == Init => VotesSafe
  BY DEF Init, VotesSafe, VotedFor

LEMMA InitOneValuePerBallot == Init => OneValuePerBallot
  BY DEF Init, OneValuePerBallot, VotedFor

LEMMA InitInv == Init => Inv
  BY InitTypeOK, InitVotesSafe, InitOneValuePerBallot DEF Inv

LEMMA InitChosenEmpty == Init => chosen = {}
PROOF
<1>1. ASSUME Init PROVE chosen = {}
  <2>1. votes = [a \in Acceptor |-> {}] BY <1>1 DEF Init
  <2>2. \A bb \in Ballot, vv \in Value : ~ ChosenAt(bb, vv)
    <3>1. SUFFICES ASSUME NEW bb \in Ballot, NEW vv \in Value
                   PROVE  ~ ChosenAt(bb, vv)
      OBVIOUS
    <3>2. SUFFICES ASSUME ChosenAt(bb, vv) PROVE FALSE
      OBVIOUS
    <3>3. PICK QQ \in Quorum : \A aa \in QQ : VotedFor(aa, bb, vv)
      BY <3>2 DEF ChosenAt
    <3>4. PICK aa \in QQ : TRUE BY QuorumNonEmpty
    <3>5. aa \in Acceptor BY <3>4, QuorumAssumption
    <3>6. VotedFor(aa, bb, vv) BY <3>3, <3>4
    <3>7. votes[aa] = {} BY <2>1, <3>5
    <3>8. <<bb, vv>> \in {} BY <3>6, <3>7 DEF VotedFor
    <3>9. QED BY <3>8
  <2>3. chosen = {} BY <2>2 DEF chosen
  <2>4. QED BY <2>3
<1>2. QED BY <1>1

-----------------------------------------------------------------------------
\* TypeOK preservation

-----------------------------------------------------------------------------
\* Helper lemmas for VotedFor prime equivalence

LEMMA VotedForPrimeEq ==
  ASSUME NEW a, NEW b, NEW v
  PROVE  VotedFor(a, b, v)' <=> (<<b, v>> \in votes'[a])
  BY DEF VotedFor

LEMMA VotedForEq ==
  ASSUME NEW a, NEW b, NEW v
  PROVE  VotedFor(a, b, v) <=> (<<b, v>> \in votes[a])
  BY DEF VotedFor

-----------------------------------------------------------------------------

LEMMA TypeOK_Step ==
  ASSUME TypeOK, [Next]_vars
  PROVE  TypeOK'
PROOF
<1>1. CASE UNCHANGED vars
  <2>1. votes' = votes BY <1>1 DEF vars
  <2>2. maxBal' = maxBal BY <1>1 DEF vars
  <2>3. QED BY <2>1, <2>2 DEF TypeOK
<1>2. CASE Next
  <2>1. PICK a \in Acceptor, b \in Ballot :
          \/ IncreaseMaxBal(a, b)
          \/ \E v \in Value : VoteFor(a, b, v)
    BY <1>2 DEF Next
  <2>2. CASE IncreaseMaxBal(a, b)
    <3>1. votes' = votes BY <2>2 DEF IncreaseMaxBal
    <3>2. maxBal' = [maxBal EXCEPT ![a] = b] BY <2>2 DEF IncreaseMaxBal
    <3>3. b \in Ballot \cup {-1} BY DEF Ballot
    <3>4. maxBal \in [Acceptor -> Ballot \cup {-1}] BY DEF TypeOK
    <3>5. maxBal' \in [Acceptor -> Ballot \cup {-1}]
      BY <3>2, <3>3, <3>4
    <3>6. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]
      BY <3>1 DEF TypeOK
    <3>7. QED BY <3>5, <3>6 DEF TypeOK
  <2>3. CASE \E v \in Value : VoteFor(a, b, v)
    <3>1. PICK v \in Value : VoteFor(a, b, v) BY <2>3
    <3>2. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
      BY <3>1 DEF VoteFor
    <3>3. maxBal' = [maxBal EXCEPT ![a] = b]
      BY <3>1 DEF VoteFor
    <3>4. votes[a] \in SUBSET (Ballot \X Value) BY DEF TypeOK
    <3>5. <<b, v>> \in Ballot \X Value BY DEF Ballot
    <3>6. votes[a] \cup {<<b, v>>} \in SUBSET (Ballot \X Value)
      BY <3>4, <3>5
    <3>7. votes \in [Acceptor -> SUBSET (Ballot \X Value)] BY DEF TypeOK
    <3>8. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]
      BY <3>2, <3>6, <3>7
    <3>9. b \in Ballot \cup {-1} BY DEF Ballot
    <3>10. maxBal \in [Acceptor -> Ballot \cup {-1}] BY DEF TypeOK
    <3>11. maxBal' \in [Acceptor -> Ballot \cup {-1}]
      BY <3>3, <3>9, <3>10
    <3>12. QED BY <3>8, <3>11 DEF TypeOK
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. QED BY <1>1, <1>2 DEF vars

-----------------------------------------------------------------------------
\* Votes monotonicity

LEMMA Votes_Monotone ==
  ASSUME TypeOK, [Next]_vars,
         NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value,
         VotedFor(a, b, v)
  PROVE  VotedFor(a, b, v)'
PROOF
<1>0. <<b, v>> \in votes[a] BY DEF VotedFor
<1>1. CASE UNCHANGED vars
  <2>1. votes' = votes BY <1>1 DEF vars
  <2>2. votes'[a] = votes[a] BY <2>1
  <2>3. <<b, v>> \in votes'[a] BY <1>0, <2>2
  <2>4. QED BY <2>3 DEF VotedFor
<1>2. CASE Next
  <2>1. PICK a2 \in Acceptor, b2 \in Ballot :
          \/ IncreaseMaxBal(a2, b2)
          \/ \E v2 \in Value : VoteFor(a2, b2, v2)
    BY <1>2 DEF Next
  <2>2. CASE IncreaseMaxBal(a2, b2)
    <3>1. votes' = votes BY <2>2 DEF IncreaseMaxBal
    <3>2. votes'[a] = votes[a] BY <3>1
    <3>3. <<b, v>> \in votes'[a] BY <1>0, <3>2
    <3>4. QED BY <3>3 DEF VotedFor
  <2>3. CASE \E v2 \in Value : VoteFor(a2, b2, v2)
    <3>1. PICK v2 \in Value : VoteFor(a2, b2, v2) BY <2>3
    <3>2. votes' = [votes EXCEPT ![a2] = votes[a2] \cup {<<b2, v2>>}]
      BY <3>1 DEF VoteFor
    <3>3. votes \in [Acceptor -> SUBSET (Ballot \X Value)] BY DEF TypeOK
    <3>4. CASE a = a2
      <4>1. votes'[a] = votes[a] \cup {<<b2, v2>>} BY <3>2, <3>4, <3>3
      <4>2. <<b, v>> \in votes'[a] BY <1>0, <4>1
      <4>3. QED BY <4>2 DEF VotedFor
    <3>5. CASE a # a2
      <4>1. votes'[a] = votes[a] BY <3>2, <3>5, <3>3
      <4>2. <<b, v>> \in votes'[a] BY <1>0, <4>1
      <4>3. QED BY <4>2 DEF VotedFor
    <3>6. QED BY <3>4, <3>5
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. QED BY <1>1, <1>2

-----------------------------------------------------------------------------
\* Chosen is monotonic

LEMMA Chosen_Monotone ==
  ASSUME TypeOK, [Next]_vars
  PROVE  chosen \subseteq chosen'
PROOF
<1>1. SUFFICES ASSUME NEW v \in chosen
               PROVE  v \in chosen'
  OBVIOUS
<1>2. v \in Value BY <1>1 DEF chosen
<1>3. PICK b \in Ballot : ChosenAt(b, v) BY <1>1 DEF chosen
<1>4. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v) BY <1>3 DEF ChosenAt
<1>5. \A a \in Q : VotedFor(a, b, v)'
  <2>1. SUFFICES ASSUME NEW a \in Q PROVE VotedFor(a, b, v)'
    OBVIOUS
  <2>2. a \in Acceptor BY QuorumAssumption
  <2>3. VotedFor(a, b, v) BY <1>4
  <2>4. QED BY Votes_Monotone, <2>2, <2>3, <1>2
<1>6. ChosenAt(b, v)' BY <1>5 DEF ChosenAt
<1>7. v \in chosen' BY <1>2, <1>3, <1>6 DEF chosen
<1>8. QED BY <1>7

-----------------------------------------------------------------------------
\* SafeAt stability

LEMMA SafeAt_Step ==
  ASSUME TypeOK, [Next]_vars,
         NEW b \in Ballot, NEW v \in Value,
         SafeAt(b, v)
  PROVE  SafeAt(b, v)'
PROOF
<1>1. SUFFICES ASSUME NEW c \in 0..(b-1)
               PROVE  NoneOtherChoosableAt(c, v)'
  BY DEF SafeAt
<1>2. NoneOtherChoosableAt(c, v) BY DEF SafeAt
<1>3. PICK Q \in Quorum : \A a \in Q : VotedFor(a, c, v) \/ CannotVoteAt(a, c)
  BY <1>2 DEF NoneOtherChoosableAt
<1>4. c \in Ballot BY DEF Ballot
<1>5. b \in Nat BY DEF Ballot
<1>6. c \in Nat BY <1>4 DEF Ballot
<1>7. c < b BY <1>5, <1>6
<1>8. \A a \in Q : VotedFor(a, c, v)' \/ CannotVoteAt(a, c)'
  <2>1. SUFFICES ASSUME NEW a \in Q
                 PROVE  VotedFor(a, c, v)' \/ CannotVoteAt(a, c)'
    OBVIOUS
  <2>2. a \in Acceptor BY QuorumAssumption
  <2>3. VotedFor(a, c, v) \/ CannotVoteAt(a, c) BY <1>3
  <2>4. CASE VotedFor(a, c, v)
    <3>1. VotedFor(a, c, v)' BY <2>2, <1>4, Votes_Monotone, <2>4
    <3>2. QED BY <3>1
  <2>5. CASE CannotVoteAt(a, c)
    <3>1. maxBal[a] > c BY <2>5 DEF CannotVoteAt
    <3>2. DidNotVoteAt(a, c) BY <2>5 DEF CannotVoteAt
    <3>3. maxBal[a] \in Ballot \cup {-1} BY <2>2 DEF TypeOK
    <3>4. maxBal[a] \in Int BY <3>3 DEF Ballot
    <3>5. CASE UNCHANGED vars
      <4>1. maxBal' = maxBal BY <3>5 DEF vars
      <4>2. votes' = votes BY <3>5 DEF vars
      <4>3. maxBal'[a] = maxBal[a] BY <4>1
      <4>4. votes'[a] = votes[a] BY <4>2
      <4>5. \A v3 \in Value : ~ VotedFor(a, c, v3)
        BY <3>2 DEF DidNotVoteAt
      <4>6. \A v3 \in Value : ~ VotedFor(a, c, v3)'
        <5>1. SUFFICES ASSUME NEW v3 \in Value PROVE ~ VotedFor(a, c, v3)'
          OBVIOUS
        <5>2. ~ VotedFor(a, c, v3) BY <4>5
        <5>3. <<c, v3>> \notin votes[a] BY <5>2 DEF VotedFor
        <5>4. <<c, v3>> \notin votes'[a] BY <5>3, <4>4
        <5>5. QED BY <5>4 DEF VotedFor
      <4>7. DidNotVoteAt(a, c)' BY <4>6 DEF DidNotVoteAt
      <4>8. maxBal[a]' > c BY <3>1, <4>3
      <4>9. CannotVoteAt(a, c)' BY <4>7, <4>8 DEF CannotVoteAt
      <4>10. QED BY <4>9
    <3>6. CASE Next
      <4>1. PICK a2 \in Acceptor, b2 \in Ballot :
              \/ IncreaseMaxBal(a2, b2)
              \/ \E v2 \in Value : VoteFor(a2, b2, v2)
        BY <3>6 DEF Next
      <4>2. CASE IncreaseMaxBal(a2, b2)
        <5>1. votes' = votes BY <4>2 DEF IncreaseMaxBal
        <5>2. maxBal' = [maxBal EXCEPT ![a2] = b2] BY <4>2 DEF IncreaseMaxBal
        <5>3. b2 > maxBal[a2] BY <4>2 DEF IncreaseMaxBal
        <5>4. b2 \in Ballot BY DEF Ballot
        <5>5. b2 \in Nat BY <5>4 DEF Ballot
        <5>6. maxBal \in [Acceptor -> Ballot \cup {-1}] BY DEF TypeOK
        <5>7. \A v3 \in Value : ~ VotedFor(a, c, v3)
          BY <3>2 DEF DidNotVoteAt
        <5>8. votes'[a] = votes[a] BY <5>1
        <5>9. \A v3 \in Value : ~ VotedFor(a, c, v3)'
          <6>1. SUFFICES ASSUME NEW v3 \in Value PROVE ~ VotedFor(a, c, v3)'
            OBVIOUS
          <6>2. ~ VotedFor(a, c, v3) BY <5>7
          <6>3. <<c, v3>> \notin votes[a] BY <6>2 DEF VotedFor
          <6>4. <<c, v3>> \notin votes'[a] BY <6>3, <5>8
          <6>5. QED BY <6>4 DEF VotedFor
        <5>10. DidNotVoteAt(a, c)' BY <5>9 DEF DidNotVoteAt
        <5>11. CASE a = a2
          <6>1. maxBal'[a] = b2 BY <5>2, <5>11, <5>6, <5>4
          <6>2. b2 > maxBal[a] BY <5>3, <5>11
          <6>3. b2 > c BY <6>2, <3>1, <5>5, <3>4
          <6>4. maxBal[a]' > c BY <6>1, <6>3
          <6>5. CannotVoteAt(a, c)' BY <5>10, <6>4 DEF CannotVoteAt
          <6>6. QED BY <6>5
        <5>12. CASE a # a2
          <6>1. maxBal'[a] = maxBal[a] BY <5>2, <5>12, <2>2, <5>6
          <6>2. maxBal[a]' > c BY <6>1, <3>1
          <6>3. CannotVoteAt(a, c)' BY <5>10, <6>2 DEF CannotVoteAt
          <6>4. QED BY <6>3
        <5>13. QED BY <5>11, <5>12
      <4>3. CASE \E v2 \in Value : VoteFor(a2, b2, v2)
        <5>1. PICK v2 \in Value : VoteFor(a2, b2, v2) BY <4>3
        <5>2. votes' = [votes EXCEPT ![a2] = votes[a2] \cup {<<b2, v2>>}]
          BY <5>1 DEF VoteFor
        <5>3. maxBal' = [maxBal EXCEPT ![a2] = b2]
          BY <5>1 DEF VoteFor
        <5>4. maxBal[a2] <= b2 BY <5>1 DEF VoteFor
        <5>5. b2 \in Ballot BY DEF Ballot
        <5>6. b2 \in Nat BY <5>5 DEF Ballot
        <5>7. maxBal \in [Acceptor -> Ballot \cup {-1}] BY DEF TypeOK
        <5>8. votes \in [Acceptor -> SUBSET (Ballot \X Value)] BY DEF TypeOK
        <5>9. CASE a = a2
          <6>1. maxBal'[a] = b2 BY <5>3, <5>9, <5>7, <5>5
          <6>2. votes'[a] = votes[a] \cup {<<b2, v2>>} BY <5>2, <5>9, <5>8
          <6>3. maxBal[a] <= b2 BY <5>4, <5>9
          <6>4. c < b2
            <7>1. maxBal[a2] \in Int BY <5>9, <3>4
            <7>2. c < maxBal[a] BY <3>1, <3>4, <5>5, <5>6
            <7>3. QED BY <7>2, <6>3, <5>6, <3>4
          <6>5. maxBal[a]' > c BY <6>1, <6>4
          <6>6. \A v3 \in Value : ~ VotedFor(a, c, v3)
            BY <3>2 DEF DidNotVoteAt
          <6>7. \A v3 \in Value : ~ VotedFor(a, c, v3)'
            <7>1. SUFFICES ASSUME NEW v3 \in Value PROVE ~ VotedFor(a, c, v3)'
              OBVIOUS
            <7>2. ~ VotedFor(a, c, v3) BY <6>6
            <7>3. <<c, v3>> \notin votes[a] BY <7>2 DEF VotedFor
            <7>4. c # b2 BY <6>4
            <7>5. <<c, v3>> # <<b2, v2>> BY <7>4
            <7>6. <<c, v3>> \notin votes[a] \cup {<<b2, v2>>} BY <7>3, <7>5
            <7>7. <<c, v3>> \notin votes'[a] BY <7>6, <6>2
            <7>8. QED BY <7>7 DEF VotedFor
          <6>8. DidNotVoteAt(a, c)' BY <6>7 DEF DidNotVoteAt
          <6>9. CannotVoteAt(a, c)' BY <6>5, <6>8 DEF CannotVoteAt
          <6>10. QED BY <6>9
        <5>10. CASE a # a2
          <6>1. maxBal'[a] = maxBal[a] BY <5>3, <5>10, <2>2, <5>7
          <6>2. votes'[a] = votes[a] BY <5>2, <5>10, <2>2, <5>8
          <6>3. \A v3 \in Value : ~ VotedFor(a, c, v3)
            BY <3>2 DEF DidNotVoteAt
          <6>4. \A v3 \in Value : ~ VotedFor(a, c, v3)'
            <7>1. SUFFICES ASSUME NEW v3 \in Value PROVE ~ VotedFor(a, c, v3)'
              OBVIOUS
            <7>2. ~ VotedFor(a, c, v3) BY <6>3
            <7>3. <<c, v3>> \notin votes[a] BY <7>2 DEF VotedFor
            <7>4. <<c, v3>> \notin votes'[a] BY <7>3, <6>2
            <7>5. QED BY <7>4 DEF VotedFor
          <6>5. DidNotVoteAt(a, c)' BY <6>4 DEF DidNotVoteAt
          <6>6. maxBal[a]' > c BY <6>1, <3>1
          <6>7. CannotVoteAt(a, c)' BY <6>5, <6>6 DEF CannotVoteAt
          <6>8. QED BY <6>7
        <5>11. QED BY <5>9, <5>10
      <4>4. QED BY <4>1, <4>2, <4>3
    <3>7. QED BY <3>5, <3>6 DEF vars
  <2>6. QED BY <2>3, <2>4, <2>5
<1>9. QED BY <1>8 DEF NoneOtherChoosableAt

-----------------------------------------------------------------------------
\* AllSafeAtZero

LEMMA AllSafeAtZero == \A v \in Value : SafeAt(0, v)
PROOF
<1>1. SUFFICES ASSUME NEW v \in Value PROVE SafeAt(0, v)
  OBVIOUS
<1>2. 0..(0-1) = {} OBVIOUS
<1>3. QED BY <1>2 DEF SafeAt

-----------------------------------------------------------------------------
\* ShowsSafety

LEMMA ShowsSafety ==
  ASSUME Inv,
         NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
         ShowsSafeAt(Q, b, v)
  PROVE  SafeAt(b, v)
PROOF
<1>1. SUFFICES ASSUME NEW d \in 0..(b-1)
               PROVE  NoneOtherChoosableAt(d, v)
  BY DEF SafeAt
<1>2. PICK c \in -1..(b-1) :
        /\ (c # -1) => \E aa \in Q : VotedFor(aa, c, v)
        /\ \A dd \in (c+1)..(b-1), aa \in Q : DidNotVoteAt(aa, dd)
  BY DEF ShowsSafeAt
<1>3. \A aa \in Q : maxBal[aa] \geq b BY DEF ShowsSafeAt
<1>4. b \in Nat BY DEF Ballot
<1>5. c \in Int /\ c >= -1 /\ c <= b - 1
  BY <1>4
<1>6. d \in Int /\ d >= 0 /\ d <= b - 1
  BY <1>4
<1>7. d < b BY <1>4, <1>6
<1>8. CASE d = c
  <2>1. c # -1 BY <1>8, <1>6
  <2>2. PICK aa \in Q : VotedFor(aa, c, v) BY <1>2, <2>1
  <2>3. VotedFor(aa, d, v) BY <2>2, <1>8
  <2>4. \A x \in Q : VotedFor(x, d, v) \/ CannotVoteAt(x, d)
    <3>1. SUFFICES ASSUME NEW x \in Q
                   PROVE  VotedFor(x, d, v) \/ CannotVoteAt(x, d)
      OBVIOUS
    <3>2. x \in Acceptor BY QuorumAssumption
    <3>3. CASE x = aa
      BY <2>3, <3>3
    <3>4. CASE x # aa
      <4>1. CASE DidNotVoteAt(x, d)
        <5>1. maxBal[x] \geq b BY <1>3
        <5>2. maxBal[x] \in Ballot \cup {-1} BY <3>2 DEF TypeOK, Inv
        <5>3. maxBal[x] \in Int BY <5>2 DEF Ballot
        <5>4. maxBal[x] > d BY <5>1, <1>7, <5>3, <1>4, <1>6
        <5>5. CannotVoteAt(x, d) BY <5>4, <4>1 DEF CannotVoteAt
        <5>6. QED BY <5>5
      <4>2. CASE ~ DidNotVoteAt(x, d)
        <5>1. \E vv \in Value : VotedFor(x, d, vv) BY <4>2 DEF DidNotVoteAt
        <5>2. PICK vv \in Value : VotedFor(x, d, vv) BY <5>1
        <5>3. aa \in Acceptor BY QuorumAssumption
        <5>4. d \in Ballot BY <1>6 DEF Ballot
        <5>5. vv = v BY <5>2, <2>3, <3>2, <5>3, <5>4 DEF OneValuePerBallot, Inv
        <5>6. VotedFor(x, d, v) BY <5>2, <5>5
        <5>7. QED BY <5>6
      <4>3. QED BY <4>1, <4>2
    <3>5. QED BY <3>3, <3>4
  <2>5. NoneOtherChoosableAt(d, v) BY <2>4 DEF NoneOtherChoosableAt
  <2>6. QED BY <2>5
<1>9. CASE d # c
  <2>1. CASE c # -1 /\ d < c
    <3>1. c \in 0..(b-1) BY <2>1, <1>5
    <3>2. PICK aa \in Q : VotedFor(aa, c, v) BY <1>2, <2>1
    <3>3. aa \in Acceptor BY QuorumAssumption
    <3>4. c \in Ballot BY <3>1 DEF Ballot
    <3>5. SafeAt(c, v) BY <3>2, <3>3, <3>4 DEF VotesSafe, Inv
    <3>6. d \in 0..(c-1) BY <2>1, <1>6, <1>5
    <3>7. NoneOtherChoosableAt(d, v) BY <3>6, <3>5 DEF SafeAt
    <3>8. QED BY <3>7
  <2>2. CASE d \in (c+1)..(b-1)
    <3>1. \A aa \in Q : DidNotVoteAt(aa, d) BY <2>2, <1>2
    <3>2. \A aa \in Q : VotedFor(aa, d, v) \/ CannotVoteAt(aa, d)
      <4>1. SUFFICES ASSUME NEW aa \in Q
                     PROVE  VotedFor(aa, d, v) \/ CannotVoteAt(aa, d)
        OBVIOUS
      <4>2. aa \in Acceptor BY QuorumAssumption
      <4>3. DidNotVoteAt(aa, d) BY <3>1
      <4>4. maxBal[aa] \geq b BY <1>3
      <4>5. maxBal[aa] \in Ballot \cup {-1} BY <4>2 DEF TypeOK, Inv
      <4>6. maxBal[aa] \in Int BY <4>5 DEF Ballot
      <4>7. maxBal[aa] > d BY <4>4, <1>7, <4>6, <1>4, <1>6
      <4>8. CannotVoteAt(aa, d) BY <4>3, <4>7 DEF CannotVoteAt
      <4>9. QED BY <4>8
    <3>3. NoneOtherChoosableAt(d, v) BY <3>2 DEF NoneOtherChoosableAt
    <3>4. QED BY <3>3
  <2>3. QED BY <2>1, <2>2, <1>9, <1>5, <1>6
<1>10. QED BY <1>8, <1>9

-----------------------------------------------------------------------------
\* OneValuePerBallot preservation

LEMMA OneValuePerBallot_Step_Specific ==
  ASSUME Inv, [Next]_vars,
         NEW a1 \in Acceptor, NEW a2 \in Acceptor,
         NEW b \in Ballot, NEW v1 \in Value, NEW v2 \in Value,
         VotedFor(a1, b, v1)', VotedFor(a2, b, v2)'
  PROVE  v1 = v2
PROOF
<1>2. CASE UNCHANGED vars
  <2>1. votes' = votes BY <1>2 DEF vars
  <2>2. votes'[a1] = votes[a1] BY <2>1
  <2>3. votes'[a2] = votes[a2] BY <2>1
  <2>4. <<b, v1>> \in votes'[a1] BY SMT DEF VotedFor
  <2>5. <<b, v2>> \in votes'[a2] BY SMT DEF VotedFor
  <2>6. VotedFor(a1, b, v1) BY <2>4, <2>2 DEF VotedFor
  <2>7. VotedFor(a2, b, v2) BY <2>5, <2>3 DEF VotedFor
  <2>8. QED BY <2>6, <2>7 DEF OneValuePerBallot, Inv
<1>3. CASE Next
  <2>1. PICK a3 \in Acceptor, b3 \in Ballot :
          \/ IncreaseMaxBal(a3, b3)
          \/ \E v3 \in Value : VoteFor(a3, b3, v3)
    BY <1>3 DEF Next
  <2>2. CASE IncreaseMaxBal(a3, b3)
    <3>1. votes' = votes BY <2>2 DEF IncreaseMaxBal
    <3>2. votes'[a1] = votes[a1] BY <3>1
    <3>3. votes'[a2] = votes[a2] BY <3>1
    <3>4. <<b, v1>> \in votes'[a1] BY DEF VotedFor
    <3>5. <<b, v2>> \in votes'[a2] BY DEF VotedFor
    <3>6. VotedFor(a1, b, v1) BY <3>4, <3>2 DEF VotedFor
    <3>7. VotedFor(a2, b, v2) BY <3>5, <3>3 DEF VotedFor
    <3>8. QED BY <3>6, <3>7 DEF OneValuePerBallot, Inv
  <2>3. CASE \E v3 \in Value : VoteFor(a3, b3, v3)
    <3>1. PICK v3 \in Value : VoteFor(a3, b3, v3) BY <2>3
    <3>2. votes' = [votes EXCEPT ![a3] = votes[a3] \cup {<<b3, v3>>}]
      BY <3>1 DEF VoteFor
    <3>3. \A vt \in votes[a3] : vt[1] # b3 BY <3>1 DEF VoteFor
    <3>4. \A c \in Acceptor \ {a3} : \A vt \in votes[c] : vt[1] = b3 => vt[2] = v3
      BY <3>1 DEF VoteFor
    <3>5. votes \in [Acceptor -> SUBSET (Ballot \X Value)] BY DEF TypeOK, Inv
    <3>6. votes'[a3] = votes[a3] \cup {<<b3, v3>>}
      BY <3>2, <3>5
    <3>7. \A x \in Acceptor : x # a3 => votes'[x] = votes[x]
      BY <3>2, <3>5
    <3>8. <<b, v1>> \in votes'[a1] BY DEF VotedFor
    <3>9. <<b, v2>> \in votes'[a2] BY DEF VotedFor
    <3>10. CASE a1 = a3 /\ a2 = a3
      <4>1. <<b, v1>> \in votes[a3] \cup {<<b3, v3>>} BY <3>8, <3>10, <3>6
      <4>2. <<b, v2>> \in votes[a3] \cup {<<b3, v3>>} BY <3>9, <3>10, <3>6
      <4>3. CASE <<b, v1>> = <<b3, v3>> /\ <<b, v2>> = <<b3, v3>>
        BY <4>3
      <4>4. CASE <<b, v1>> = <<b3, v3>> /\ <<b, v2>> \in votes[a3]
        <5>1. b = b3 BY <4>4
        <5>2. v1 = v3 BY <4>4
        <5>3. <<b, v2>> \in votes[a3] BY <4>4
        <5>4. (<<b, v2>>)[1] = b BY <5>3
        <5>5. \E vt \in votes[a3] : vt[1] = b3 BY <5>3, <5>4, <5>1
        <5>6. FALSE BY <5>5, <3>3
        <5>7. QED BY <5>6
      <4>5. CASE <<b, v1>> \in votes[a3] /\ <<b, v2>> = <<b3, v3>>
        <5>1. b = b3 BY <4>5
        <5>2. <<b, v1>> \in votes[a3] BY <4>5
        <5>3. (<<b, v1>>)[1] = b BY <5>2
        <5>4. \E vt \in votes[a3] : vt[1] = b3 BY <5>2, <5>3, <5>1
        <5>5. FALSE BY <5>4, <3>3
        <5>6. QED BY <5>5
      <4>6. CASE <<b, v1>> \in votes[a3] /\ <<b, v2>> \in votes[a3]
        <5>1. VotedFor(a3, b, v1) BY <4>6 DEF VotedFor
        <5>2. VotedFor(a3, b, v2) BY <4>6 DEF VotedFor
        <5>3. QED BY <5>1, <5>2 DEF OneValuePerBallot, Inv
      <4>7. QED BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6
    <3>11. CASE a1 = a3 /\ a2 # a3
      <4>1. <<b, v1>> \in votes[a3] \cup {<<b3, v3>>} BY <3>8, <3>11, <3>6
      <4>2. votes'[a2] = votes[a2] BY <3>7, <3>11
      <4>3. <<b, v2>> \in votes[a2] BY <3>9, <4>2
      <4>4. VotedFor(a2, b, v2) BY <4>3 DEF VotedFor
      <4>5. CASE <<b, v1>> = <<b3, v3>>
        <5>1. b = b3 BY <4>5
        <5>2. v1 = v3 BY <4>5
        <5>3. (<<b, v2>>)[1] = b BY <4>3
        <5>4. (<<b, v2>>)[1] = b3 BY <5>3, <5>1
        <5>5. (<<b, v2>>)[2] = v3 BY <3>4, <4>3, <3>11, <5>4
        <5>6. v2 = v3 BY <5>5
        <5>7. QED BY <5>2, <5>6
      <4>6. CASE <<b, v1>> \in votes[a3]
        <5>1. VotedFor(a3, b, v1) BY <4>6 DEF VotedFor
        <5>2. QED BY <5>1, <4>4 DEF OneValuePerBallot, Inv
      <4>7. QED BY <4>1, <4>5, <4>6
    <3>12. CASE a1 # a3 /\ a2 = a3
      <4>1. <<b, v2>> \in votes[a3] \cup {<<b3, v3>>} BY <3>9, <3>12, <3>6
      <4>2. votes'[a1] = votes[a1] BY <3>7, <3>12
      <4>3. <<b, v1>> \in votes[a1] BY <3>8, <4>2
      <4>4. VotedFor(a1, b, v1) BY <4>3 DEF VotedFor
      <4>5. CASE <<b, v2>> = <<b3, v3>>
        <5>1. b = b3 BY <4>5
        <5>2. v2 = v3 BY <4>5
        <5>3. (<<b, v1>>)[1] = b BY <4>3
        <5>4. (<<b, v1>>)[1] = b3 BY <5>3, <5>1
        <5>5. (<<b, v1>>)[2] = v3 BY <3>4, <4>3, <3>12, <5>4
        <5>6. v1 = v3 BY <5>5
        <5>7. QED BY <5>2, <5>6
      <4>6. CASE <<b, v2>> \in votes[a3]
        <5>1. VotedFor(a3, b, v2) BY <4>6 DEF VotedFor
        <5>2. QED BY <5>1, <4>4 DEF OneValuePerBallot, Inv
      <4>7. QED BY <4>1, <4>5, <4>6
    <3>13. CASE a1 # a3 /\ a2 # a3
      <4>1. votes'[a1] = votes[a1] BY <3>7, <3>13
      <4>2. votes'[a2] = votes[a2] BY <3>7, <3>13
      <4>3. <<b, v1>> \in votes[a1] BY <3>8, <4>1
      <4>4. <<b, v2>> \in votes[a2] BY <3>9, <4>2
      <4>5. VotedFor(a1, b, v1) BY <4>3 DEF VotedFor
      <4>6. VotedFor(a2, b, v2) BY <4>4 DEF VotedFor
      <4>7. QED BY <4>5, <4>6 DEF OneValuePerBallot, Inv
    <3>14. QED BY <3>10, <3>11, <3>12, <3>13
  <2>4. QED BY <2>1, <2>2, <2>3
<1>4. QED BY <1>2, <1>3 DEF vars

LEMMA OneValuePerBallot_Step ==
  ASSUME Inv, [Next]_vars
  PROVE  OneValuePerBallot'
  BY OneValuePerBallot_Step_Specific DEF OneValuePerBallot

-----------------------------------------------------------------------------
\* VotesSafe preservation

LEMMA VotesSafe_Step_Specific ==
  ASSUME Inv, [Next]_vars,
         NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value,
         VotedFor(a, b, v)'
  PROVE  SafeAt(b, v)'
PROOF
<1>2. TypeOK BY DEF Inv
<1>3. CASE UNCHANGED vars
  <2>1. votes' = votes BY <1>3 DEF vars
  <2>2. votes'[a] = votes[a] BY <2>1
  <2>3. <<b, v>> \in votes'[a] BY DEF VotedFor
  <2>4. VotedFor(a, b, v) BY <2>3, <2>2 DEF VotedFor
  <2>5. SafeAt(b, v) BY <2>4 DEF VotesSafe, Inv
  <2>6. QED BY <2>5, <1>2, <1>3, SafeAt_Step
<1>4. CASE Next
  <2>1. PICK a3 \in Acceptor, b3 \in Ballot :
          \/ IncreaseMaxBal(a3, b3)
          \/ \E v3 \in Value : VoteFor(a3, b3, v3)
    BY <1>4 DEF Next
  <2>2. CASE IncreaseMaxBal(a3, b3)
    <3>1. votes' = votes BY <2>2 DEF IncreaseMaxBal
    <3>2. votes'[a] = votes[a] BY <3>1
    <3>3. <<b, v>> \in votes'[a] BY DEF VotedFor
    <3>4. VotedFor(a, b, v) BY <3>3, <3>2 DEF VotedFor
    <3>5. SafeAt(b, v) BY <3>4 DEF VotesSafe, Inv
    <3>6. QED BY <3>5, <1>2, <1>4, SafeAt_Step
  <2>3. CASE \E v3 \in Value : VoteFor(a3, b3, v3)
    <3>1. PICK v3 \in Value : VoteFor(a3, b3, v3) BY <2>3
    <3>2. votes' = [votes EXCEPT ![a3] = votes[a3] \cup {<<b3, v3>>}]
      BY <3>1 DEF VoteFor
    <3>3. \E Q \in Quorum : ShowsSafeAt(Q, b3, v3) BY <3>1 DEF VoteFor
    <3>4. votes \in [Acceptor -> SUBSET (Ballot \X Value)] BY DEF TypeOK, Inv
    <3>5. votes'[a3] = votes[a3] \cup {<<b3, v3>>}
      BY <3>2, <3>4
    <3>6. \A x \in Acceptor : x # a3 => votes'[x] = votes[x]
      BY <3>2, <3>4
    <3>7. <<b, v>> \in votes'[a] BY DEF VotedFor
    <3>8. CASE a = a3
      <4>1. <<b, v>> \in votes[a3] \cup {<<b3, v3>>} BY <3>7, <3>8, <3>5
      <4>2. CASE <<b, v>> = <<b3, v3>>
        <5>1. b = b3 BY <4>2
        <5>2. v = v3 BY <4>2
        <5>3. PICK Q \in Quorum : ShowsSafeAt(Q, b3, v3) BY <3>3
        <5>4. SafeAt(b3, v3) BY <5>3, ShowsSafety
        <5>5. SafeAt(b, v) BY <5>1, <5>2, <5>4
        <5>6. QED BY <5>5, <1>2, <1>4, SafeAt_Step
      <4>3. CASE <<b, v>> \in votes[a3]
        <5>1. VotedFor(a3, b, v) BY <4>3 DEF VotedFor
        <5>2. SafeAt(b, v) BY <5>1 DEF VotesSafe, Inv
        <5>3. QED BY <5>2, <1>2, <1>4, SafeAt_Step
      <4>4. QED BY <4>1, <4>2, <4>3
    <3>9. CASE a # a3
      <4>1. votes'[a] = votes[a] BY <3>6, <3>9
      <4>2. <<b, v>> \in votes[a] BY <3>7, <4>1
      <4>3. VotedFor(a, b, v) BY <4>2 DEF VotedFor
      <4>4. SafeAt(b, v) BY <4>3 DEF VotesSafe, Inv
      <4>5. QED BY <4>4, <1>2, <1>4, SafeAt_Step
    <3>10. QED BY <3>8, <3>9
  <2>4. QED BY <2>1, <2>2, <2>3
<1>5. QED BY <1>3, <1>4 DEF vars

LEMMA VotesSafe_Step ==
  ASSUME Inv, [Next]_vars
  PROVE  VotesSafe'
  BY VotesSafe_Step_Specific DEF VotesSafe

-----------------------------------------------------------------------------
\* Inv preservation

LEMMA Inv_Step ==
  ASSUME Inv, [Next]_vars
  PROVE  Inv'
PROOF
<1>1. TypeOK BY DEF Inv
<1>2. TypeOK' BY <1>1, TypeOK_Step
<1>3. VotesSafe' BY VotesSafe_Step
<1>4. OneValuePerBallot' BY OneValuePerBallot_Step
<1>5. QED BY <1>2, <1>3, <1>4 DEF Inv

LEMMA Spec_Inv == Spec => []Inv
PROOF
<1>1. Init => Inv BY InitInv
<1>2. Inv /\ [Next]_vars => Inv' BY Inv_Step
<1>3. QED BY <1>1, <1>2, PTL DEF Spec, vars

-----------------------------------------------------------------------------
\* OneVote follows from OneValuePerBallot

LEMMA OneVote_Lemma ==
  ASSUME Inv,
         NEW a \in Acceptor, NEW b \in Ballot,
         NEW v \in Value, NEW w \in Value,
         VotedFor(a, b, v), VotedFor(a, b, w)
  PROVE  v = w
  BY DEF OneValuePerBallot, Inv

-----------------------------------------------------------------------------
\* Inv implies ChosenSingleton

LEMMA Inv_ChosenSingleton_Specific ==
  ASSUME Inv, NEW v1 \in chosen, NEW v2 \in chosen
  PROVE  v1 = v2
PROOF
<1>2. v1 \in Value /\ v2 \in Value BY DEF chosen
<1>3. PICK b1 \in Ballot : ChosenAt(b1, v1) BY DEF chosen
<1>4. PICK b2 \in Ballot : ChosenAt(b2, v2) BY DEF chosen
<1>5. PICK Q1 \in Quorum : \A a \in Q1 : VotedFor(a, b1, v1) BY <1>3 DEF ChosenAt
<1>6. PICK Q2 \in Quorum : \A a \in Q2 : VotedFor(a, b2, v2) BY <1>4 DEF ChosenAt
<1>7. CASE b1 = b2
  <2>1. Q1 \cap Q2 # {} BY QuorumAssumption
  <2>2. PICK a \in Q1 \cap Q2 : TRUE BY <2>1
  <2>3. VotedFor(a, b1, v1) BY <1>5, <2>2
  <2>4. VotedFor(a, b2, v2) BY <1>6, <2>2
  <2>5. VotedFor(a, b1, v2) BY <2>4, <1>7
  <2>6. a \in Acceptor BY QuorumAssumption, <2>2
  <2>7. v1 = v2
    <3>1. \A aa \in Acceptor, bb \in Ballot, vv \in Value, ww \in Value :
            VotedFor(aa, bb, vv) /\ VotedFor(aa, bb, ww) => vv = ww
      BY DEF OneValuePerBallot, Inv
    <3>2. QED BY <3>1, <2>3, <2>5, <2>6, <1>2
  <2>8. QED BY <2>7
<1>8. CASE b1 # b2
  <2>1. CASE b1 < b2
    <3>1. Q2 # {} BY QuorumNonEmpty
    <3>2. PICK a \in Q2 : TRUE BY <3>1
    <3>3. VotedFor(a, b2, v2) BY <1>6, <3>2
    <3>4. a \in Acceptor BY QuorumAssumption, <3>2
    <3>5. SafeAt(b2, v2)
      <4>1. \A aa \in Acceptor, bb \in Ballot, vv \in Value :
              VotedFor(aa, bb, vv) => SafeAt(bb, vv)
        BY DEF VotesSafe, Inv
      <4>2. VotedFor(a, b2, v2) => SafeAt(b2, v2)
        BY <4>1, <3>4, <1>2
      <4>3. QED BY <4>2, <3>3
    <3>6. b1 \in 0..(b2 - 1) BY <2>1 DEF Ballot
    <3>7. NoneOtherChoosableAt(b1, v2) BY <3>5, <3>6 DEF SafeAt
    <3>8. PICK Q3 \in Quorum :
           \A a3 \in Q3 : VotedFor(a3, b1, v2) \/ CannotVoteAt(a3, b1)
      BY <3>7 DEF NoneOtherChoosableAt
    <3>9. Q1 \cap Q3 # {} BY QuorumAssumption
    <3>10. PICK x \in Q1 \cap Q3 : TRUE BY <3>9
    <3>11. x \in Acceptor BY QuorumAssumption, <3>10
    <3>12. VotedFor(x, b1, v1) BY <1>5, <3>10
    <3>13. VotedFor(x, b1, v2) \/ CannotVoteAt(x, b1) BY <3>8, <3>10
    <3>14. ~ CannotVoteAt(x, b1)
      <4>1. ~ DidNotVoteAt(x, b1)
        <5>1. SUFFICES ASSUME DidNotVoteAt(x, b1) PROVE FALSE
          OBVIOUS
        <5>2. ~ VotedFor(x, b1, v1) BY <5>1, <1>2 DEF DidNotVoteAt
        <5>3. QED BY <5>2, <3>12
      <4>2. QED BY <4>1 DEF CannotVoteAt
    <3>15. VotedFor(x, b1, v2) BY <3>13, <3>14
    <3>16. v1 = v2
      <4>1. \A aa \in Acceptor, bb \in Ballot, vv \in Value, ww \in Value :
              VotedFor(aa, bb, vv) /\ VotedFor(aa, bb, ww) => vv = ww
        BY DEF OneValuePerBallot, Inv
      <4>2. QED BY <4>1, <3>11, <3>12, <3>15, <1>2
    <3>17. QED BY <3>16
  <2>2. CASE b2 < b1
    <3>1. Q1 # {} BY QuorumNonEmpty
    <3>2. PICK a \in Q1 : TRUE BY <3>1
    <3>3. VotedFor(a, b1, v1) BY <1>5, <3>2
    <3>4. a \in Acceptor BY QuorumAssumption, <3>2
    <3>5. SafeAt(b1, v1)
      <4>1. \A aa \in Acceptor, bb \in Ballot, vv \in Value :
              VotedFor(aa, bb, vv) => SafeAt(bb, vv)
        BY DEF VotesSafe, Inv
      <4>2. VotedFor(a, b1, v1) => SafeAt(b1, v1)
        BY <4>1, <3>4, <1>2
      <4>3. QED BY <4>2, <3>3
    <3>6. b2 \in 0..(b1 - 1) BY <2>2 DEF Ballot
    <3>7. NoneOtherChoosableAt(b2, v1) BY <3>5, <3>6 DEF SafeAt
    <3>8. PICK Q3 \in Quorum :
           \A a3 \in Q3 : VotedFor(a3, b2, v1) \/ CannotVoteAt(a3, b2)
      BY <3>7 DEF NoneOtherChoosableAt
    <3>9. Q2 \cap Q3 # {} BY QuorumAssumption
    <3>10. PICK x \in Q2 \cap Q3 : TRUE BY <3>9
    <3>11. x \in Acceptor BY QuorumAssumption, <3>10
    <3>12. VotedFor(x, b2, v2) BY <1>6, <3>10
    <3>13. VotedFor(x, b2, v1) \/ CannotVoteAt(x, b2) BY <3>8, <3>10
    <3>14. ~ CannotVoteAt(x, b2)
      <4>1. ~ DidNotVoteAt(x, b2)
        <5>1. SUFFICES ASSUME DidNotVoteAt(x, b2) PROVE FALSE
          OBVIOUS
        <5>2. ~ VotedFor(x, b2, v2) BY <5>1, <1>2 DEF DidNotVoteAt
        <5>3. QED BY <5>2, <3>12
      <4>2. QED BY <4>1 DEF CannotVoteAt
    <3>15. VotedFor(x, b2, v1) BY <3>13, <3>14
    <3>16. v1 = v2
      <4>1. \A aa \in Acceptor, bb \in Ballot, vv \in Value, ww \in Value :
              VotedFor(aa, bb, vv) /\ VotedFor(aa, bb, ww) => vv = ww
        BY DEF OneValuePerBallot, Inv
      <4>2. QED BY <4>1, <3>11, <3>15, <3>12, <1>2
    <3>17. QED BY <3>16
  <2>3. QED BY <2>1, <2>2, <1>8 DEF Ballot
<1>9. QED BY <1>7, <1>8

LEMMA Inv_ChosenSingleton == Inv => ChosenSingleton
  BY Inv_ChosenSingleton_Specific DEF ChosenSingleton

-----------------------------------------------------------------------------
\* Refinement step

LEMMA Refinement_Step ==
  ASSUME Inv, Inv', [Next]_vars
  PROVE  [C!Next]_chosen
PROOF
<1>1. SUFFICES ASSUME chosen' # chosen
               PROVE  C!Next
  BY DEF C!Next
<1>2. TypeOK BY DEF Inv
<1>3. chosen \subseteq chosen' BY Chosen_Monotone, <1>2
<1>4. chosen' \ chosen # {}
  <2>1. SUFFICES ASSUME chosen' \ chosen = {} PROVE FALSE
    OBVIOUS
  <2>2. chosen' \subseteq chosen BY <2>1
  <2>3. chosen' = chosen BY <2>2, <1>3
  <2>4. QED BY <2>3, <1>1
<1>5. PICK v \in chosen' \ chosen : TRUE BY <1>4
<1>6. v \in chosen' BY <1>5
<1>7. v \notin chosen BY <1>5
<1>8. v \in Value BY <1>6 DEF chosen
<1>9. ChosenSingleton' BY Inv_ChosenSingleton, Inv', PTL
<1>10. \A v0 \in chosen', w0 \in chosen' : v0 = w0
  BY <1>9 DEF ChosenSingleton
<1>11. chosen = {}
  <2>1. SUFFICES ASSUME chosen # {} PROVE FALSE
    OBVIOUS
  <2>2. PICK w \in chosen : TRUE BY <2>1
  <2>3. w \in chosen' BY <2>2, <1>3
  <2>4. v = w BY <1>10, <1>6, <2>3
  <2>5. v # w BY <1>7, <2>2
  <2>6. QED BY <2>4, <2>5
<1>12. chosen' = {v}
  <2>1. SUFFICES ASSUME NEW w \in chosen', w # v PROVE FALSE
    BY <1>6
  <2>2. v = w BY <1>10, <1>6, <2>1
  <2>3. QED BY <2>1, <2>2
<1>13. \E v0 \in Value : chosen' = {v0} BY <1>8, <1>12
<1>14. QED BY <1>11, <1>13 DEF C!Next

-----------------------------------------------------------------------------
\* Main refinement theorem

THEOREM Refinement == Spec => C!Spec
PROOF
<1>1. Init => C!Init BY InitChosenEmpty DEF C!Init
<1>2. Inv /\ Inv' /\ [Next]_vars => [C!Next]_chosen BY Refinement_Step
<1>3. Spec => []Inv BY Spec_Inv
<1>4. Spec => [][Next]_vars BY PTL DEF Spec, vars
<1>5. Spec => Init BY PTL DEF Spec
<1>6. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF Spec, C!Spec
=============================================================================
