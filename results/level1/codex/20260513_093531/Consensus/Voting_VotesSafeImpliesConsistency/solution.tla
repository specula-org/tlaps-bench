------------------------------- MODULE Voting_VotesSafeImpliesConsistency -------------------------------
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
PROOF
<1>1. \E v \in chosen : TRUE
    BY DEF chosen
<1>2. PICK v \in chosen : TRUE
    BY <1>1
<1>3. v \in Value /\ \E b \in Ballot : ChosenAt(b, v)
    BY <1>2 DEF chosen
<1>4. PICK b \in Ballot : ChosenAt(b, v)
    BY <1>3
<1>5. \A w \in chosen : w = v
    <2>1. TAKE w \in chosen
    <2>2. w \in Value /\ \E c \in Ballot : ChosenAt(c, w)
      BY <2>1 DEF chosen
    <2>3. PICK c \in Ballot : ChosenAt(c, w)
      BY <2>2
    <2>4. CASE b = c
      <3>1. PICK Q1 \in Quorum : \A a \in Q1 : VotedFor(a, b, v)
        BY <1>4 DEF ChosenAt
      <3>2. PICK Q2 \in Quorum : \A a \in Q2 : VotedFor(a, c, w)
        BY <2>3 DEF ChosenAt
      <3>3. Q1 \cap Q2 # {}
        BY <3>1, <3>2, QuorumAssumption
      <3>4. PICK a \in Q1 \cap Q2 : TRUE
        BY <3>3
      <3>5. a \in Acceptor /\ VotedFor(a, b, v) /\ VotedFor(a, b, w)
        BY <3>1, <3>2, <3>4, <2>4, QuorumAssumption
      <3> QED
        BY <3>5, <1>3, <2>2, <1>4, OneVote DEF OneVote
    <2>5. CASE b < c
      <3>1. PICK Qc \in Quorum : \A a \in Qc : VotedFor(a, c, w)
        BY <2>3 DEF ChosenAt
      <3>2. Qc # {}
        BY <3>1, QuorumNonEmpty
      <3>3. PICK ac \in Qc : TRUE
        BY <3>2
      <3>4. ac \in Acceptor /\ VotedFor(ac, c, w)
        BY <3>1, <3>3, QuorumAssumption
      <3>5. SafeAt(c, w)
        BY <3>4, <2>2, VotesSafe DEF VotesSafe
      <3>6. b \in 0..(c-1)
        BY <1>4, <2>3, <2>5 DEF Ballot
      <3>7. NoneOtherChoosableAt(b, w)
        BY <3>5, <3>6 DEF SafeAt
      <3>8. PICK Qn \in Quorum :
              \A a \in Qn : VotedFor(a, b, w) \/ CannotVoteAt(a, b)
        BY <3>7 DEF NoneOtherChoosableAt
      <3>9. PICK Qb \in Quorum : \A a \in Qb : VotedFor(a, b, v)
        BY <1>4 DEF ChosenAt
      <3>10. Qn \cap Qb # {}
        BY <3>8, <3>9, QuorumAssumption
      <3>11. PICK a \in Qn \cap Qb : TRUE
        BY <3>10
      <3>12. a \in Acceptor /\ VotedFor(a, b, v) /\
              (VotedFor(a, b, w) \/ CannotVoteAt(a, b))
        BY <3>8, <3>9, <3>11, QuorumAssumption
      <3>13. VotedFor(a, b, w)
        <4>1. SUFFICES ASSUME CannotVoteAt(a, b) PROVE FALSE
          BY <3>12
        <4>2. DidNotVoteAt(a, b)
          BY <4>1 DEF CannotVoteAt
        <4>3. ~ VotedFor(a, b, v)
          BY <4>2, <1>3 DEF DidNotVoteAt
        <4> QED
          BY <3>12, <4>3
      <3> QED
        BY <3>12, <3>13, <1>3, <2>2, <1>4, OneVote DEF OneVote
    <2>6. CASE c < b
      <3>1. PICK Qb \in Quorum : \A a \in Qb : VotedFor(a, b, v)
        BY <1>4 DEF ChosenAt
      <3>2. Qb # {}
        BY <3>1, QuorumNonEmpty
      <3>3. PICK ab \in Qb : TRUE
        BY <3>2
      <3>4. ab \in Acceptor /\ VotedFor(ab, b, v)
        BY <3>1, <3>3, QuorumAssumption
      <3>5. SafeAt(b, v)
        BY <3>4, <1>3, VotesSafe DEF VotesSafe
      <3>6. c \in 0..(b-1)
        BY <1>4, <2>3, <2>6 DEF Ballot
      <3>7. NoneOtherChoosableAt(c, v)
        BY <3>5, <3>6 DEF SafeAt
      <3>8. PICK Qn \in Quorum :
              \A a \in Qn : VotedFor(a, c, v) \/ CannotVoteAt(a, c)
        BY <3>7 DEF NoneOtherChoosableAt
      <3>9. PICK Qc \in Quorum : \A a \in Qc : VotedFor(a, c, w)
        BY <2>3 DEF ChosenAt
      <3>10. Qn \cap Qc # {}
        BY <3>8, <3>9, QuorumAssumption
      <3>11. PICK a \in Qn \cap Qc : TRUE
        BY <3>10
      <3>12. a \in Acceptor /\ VotedFor(a, c, w) /\
              (VotedFor(a, c, v) \/ CannotVoteAt(a, c))
        BY <3>8, <3>9, <3>11, QuorumAssumption
      <3>13. VotedFor(a, c, v)
        <4>1. SUFFICES ASSUME CannotVoteAt(a, c) PROVE FALSE
          BY <3>12
        <4>2. DidNotVoteAt(a, c)
          BY <4>1 DEF CannotVoteAt
        <4>3. ~ VotedFor(a, c, w)
          BY <4>2, <2>2 DEF DidNotVoteAt
        <4> QED
          BY <3>12, <4>3
      <3> QED
        BY <3>12, <3>13, <1>3, <2>2, <2>3, OneVote DEF OneVote
    <2> QED
      BY <2>4, <2>5, <2>6, <1>4, <2>3 DEF Ballot
<1>6. chosen \subseteq {v}
    BY <1>5
<1>7. {v} \subseteq chosen
    BY <1>2
<1>8. chosen = {v}
    BY <1>6, <1>7
<1> QED
  BY <1>3, <1>8

=============================================================================
