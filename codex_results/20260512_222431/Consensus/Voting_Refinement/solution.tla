------------------------------- MODULE Voting_Refinement -------------------------------
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
  PROOF OMITTED

THEOREM SafeAtStable == Inv /\ Next /\ TypeOK' =>
                            \A b \in Ballot, v \in Value :
                                SafeAt(b, v) => SafeAt(b, v)'
  OMITTED                                
-----------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
  PROOF OMITTED

----------------------------------------------------------------------------
THEOREM Consistent == Spec => []Consistency
  PROOF OMITTED

----------------------------------------------------------------------------
C == INSTANCE Consensus \* WITH chosen <- chosen

THEOREM Refinement == Spec => C!Spec
PROOF
  <1>1. Init => C!Init
  PROOF
    <2>1. ASSUME Init
           PROVE  \A v \in Value : ~ \E b \in Ballot : ChosenAt(b, v)
    PROOF
      <3>1. TAKE v \in Value
      <3>2. ASSUME \E b \in Ballot : ChosenAt(b, v)
             PROVE FALSE
      PROOF
        <4>1. PICK b \in Ballot : ChosenAt(b, v)
          BY <3>2
        <4>2. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
          BY <4>1 DEF ChosenAt
        <4>3. PICK a \in Q : TRUE
          BY <4>2, QuorumNonEmpty
        <4>4. a \in Acceptor
          BY <4>2, <4>3, QuorumAssumption
        <4>5. VotedFor(a, b, v)
          BY <4>2, <4>3
        <4>6. votes[a] = {}
          BY <2>1, <4>4 DEF Init
        <4>7. QED BY <4>5, <4>6 DEF VotedFor
      <3>3. QED BY <3>2
    <2>2. QED BY <2>1 DEF C!Init, chosen
  <1>1a. ASSUME votes' = votes
          PROVE  chosen' = chosen
    BY <1>1a DEF chosen, ChosenAt, VotedFor
  <1>2. ASSUME Next
         PROVE  chosen \subseteq chosen'
  PROOF
    <2>1. \A x \in Acceptor, bb \in Ballot, vv \in Value :
            <<bb, vv>> \in votes[x] => <<bb, vv>> \in votes'[x]
    PROOF
      <3>1. TAKE x \in Acceptor, bb \in Ballot, vv \in Value
      <3>2. ASSUME <<bb, vv>> \in votes[x]
             PROVE <<bb, vv>> \in votes'[x]
      PROOF
        <4>1. PICK aa \in Acceptor, b \in Ballot :
                \/ IncreaseMaxBal(aa, b)
                \/ \E v \in Value : VoteFor(aa, b, v)
          BY <1>2 DEF Next
        <4>2. CASE IncreaseMaxBal(aa, b)
          BY <3>2, <4>2 DEF IncreaseMaxBal
        <4>3. CASE \E v \in Value : VoteFor(aa, b, v)
        PROOF
          <5>1. PICK v \in Value : VoteFor(aa, b, v)
            BY <4>3
          <5>2. CASE x = aa
            BY <3>2, <5>1 DEF VoteFor
          <5>3. CASE x # aa
            BY <3>2, <5>1 DEF VoteFor
          <5>4. QED BY <5>2, <5>3
        <4>4. QED BY <4>1, <4>2, <4>3
      <3>3. QED BY <3>2
    <2>2. \A vv \in chosen : vv \in chosen'
    PROOF
      <3>1. TAKE vv \in chosen
      <3>2. vv \in Value /\ \E bb \in Ballot : ChosenAt(bb, vv)
        BY <3>1 DEF chosen
      <3>3. PICK bb \in Ballot : ChosenAt(bb, vv)
        BY <3>2
      <3>4. PICK Q \in Quorum : \A x \in Q : VotedFor(x, bb, vv)
        BY <3>3 DEF ChosenAt
      <3>5. \A x \in Q : x \in Acceptor
        BY <3>4, QuorumAssumption
      <3>6. \A x \in Q : <<bb, vv>> \in votes'[x]
        BY <2>1, <3>2, <3>4, <3>5 DEF VotedFor
      <3>7. \E Q \in Quorum : \A x \in Q : <<bb, vv>> \in votes'[x]
        BY <3>4, <3>6
      <3>8. vv \in chosen'
        BY <3>2, <3>7 DEF chosen, ChosenAt, VotedFor
      <3>9. QED BY <3>8
    <2>3. QED BY <2>2
  <1>3. ASSUME UNCHANGED <<votes, maxBal>>
         PROVE  UNCHANGED chosen
    BY <1>3, <1>1a
  <1>4. ASSUME Next, Consistency, Consistency'
         PROVE  [C!Next]_chosen
  PROOF
    <2>1. CASE chosen' = chosen
      BY <2>1 DEF C!Next
    <2>2. CASE chosen' # chosen
    PROOF
      <3>1. chosen \subseteq chosen'
        BY <1>4, <1>2
      <3>2. chosen = {}
        BY <1>4, <2>2, <3>1 DEF Consistency
      <3>3. \E v \in Value : chosen' = {v}
        BY <1>4, <2>2, <3>1 DEF Consistency
      <3>4. C!Next
        BY <3>2, <3>3 DEF C!Next
      <3>5. QED BY <3>4 DEF C!Next
    <2>3. QED BY <2>1, <2>2
  <1>5. ASSUME [Next]_<<votes, maxBal>>, Consistency, Consistency'
         PROVE  [C!Next]_chosen
  PROOF
    <2>1. CASE Next
      BY <1>5, <2>1, <1>4
    <2>2. CASE UNCHANGED <<votes, maxBal>>
      BY <1>5, <2>2, <1>3 DEF C!Next
    <2>3. QED BY <1>5, <2>1, <2>2 DEF C!Next
  <1>6. []Consistency /\ [][Next]_<<votes, maxBal>> => [][C!Next]_chosen
    BY <1>5, PTL
  <1>7. Spec => []Consistency
    BY Consistent
  <1>8. QED BY <1>1, <1>6, <1>7 DEF Spec, C!Spec

=============================================================================
