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
<1>1. Init => chosen = {}
  PROOF
  <2>1. ASSUME Init
        PROVE chosen = {}
    PROOF
    <3>1. ASSUME NEW v \in chosen
        PROVE  FALSE
      PROOF
      <4>1. v \in Value /\ \E b \in Ballot : ChosenAt(b, v)
        BY <3>1 DEF chosen
      <4>2. PICK b \in Ballot : ChosenAt(b, v)
        BY <4>1
      <4>3. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
        BY <4>2 DEF ChosenAt
      <4>4. Q # {}
        BY <4>3, QuorumNonEmpty
      <4>5. PICK a \in Q : TRUE
        BY <4>4
      <4>6. VotedFor(a, b, v)
        BY <4>3, <4>5
      <4>7. a \in Acceptor
        BY <4>3, <4>5, QuorumAssumption
      <4>8. votes[a] = {}
        BY <2>1, <4>7, SMT DEF Init
      <4>9. FALSE
        BY <4>6, <4>8 DEF VotedFor
      <4> QED BY <4>9
    <3> QED BY <3>1, IsaWithSetExtensionality
  <2> QED BY <2>1
<1>2. \A a \in Acceptor, b \in Ballot : IncreaseMaxBal(a, b) => chosen \subseteq chosen'
  PROOF
  <2>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot, IncreaseMaxBal(a, b)
        PROVE chosen \subseteq chosen'
    PROOF
    <3>1. UNCHANGED votes
      BY <2>1 DEF IncreaseMaxBal
    <3>2. votes' = votes
      BY <3>1
    <3>3. \A c, d, u : VotedFor(c, d, u) => VotedFor(c, d, u)'
      BY <3>2 DEF VotedFor
    <3>4. ASSUME NEW u \in chosen
        PROVE  u \in chosen'
      BY <3>3 DEF chosen, ChosenAt
    <3> QED BY <3>4
  <2> QED BY <2>1
<1>3. \A a \in Acceptor, b \in Ballot, w \in Value : VoteFor(a, b, w) => chosen \subseteq chosen'
  PROOF
  <2>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot,
               NEW w \in Value, VoteFor(a, b, w)
        PROVE chosen \subseteq chosen'
    PROOF
    <3>1. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, w>>}]
      BY <2>1 DEF VoteFor
    <3>2. \A c \in Acceptor : votes[c] \subseteq votes'[c]
      PROOF
      <4>1. ASSUME NEW c \in Acceptor, NEW vt \in votes[c]
          PROVE  vt \in votes'[c]
        PROOF
        <5>1. CASE c = a
          BY <3>1, <4>1, SMT
        <5>2. CASE c # a
          BY <3>1, <4>1, SMT
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>1
    <3>3. \A c \in Acceptor, d, u : VotedFor(c, d, u) => VotedFor(c, d, u)'
      BY <3>2 DEF VotedFor
    <3>4. ASSUME NEW u \in chosen
        PROVE  u \in chosen'
      PROOF
      <4>1. u \in Value /\ \E d \in Ballot : ChosenAt(d, u)
        BY <3>4 DEF chosen
      <4>2. PICK d \in Ballot : ChosenAt(d, u)
        BY <4>1
      <4>3. PICK Q \in Quorum : \A c \in Q : VotedFor(c, d, u)
        BY <4>2 DEF ChosenAt
      <4>4. \A c \in Q : VotedFor(c, d, u)'
        BY <3>3, <4>3, QuorumAssumption
      <4>5. ChosenAt(d, u)'
        BY <4>3, <4>4 DEF ChosenAt
      <4>6. \E d \in Ballot : ChosenAt(d, u)'
        BY <4>2, <4>5
      <4> QED BY <4>1, <4>6 DEF chosen
    <3> QED BY <3>4
  <2> QED BY <2>1
<1>4. Next => chosen \subseteq chosen'
  BY <1>2, <1>3 DEF Next
<1>5. Consistency /\ Consistency' /\ [Next]_<<votes, maxBal>>
        => ( ( /\ chosen = {}
               /\ \E v \in Value : chosen' = {v} )
             \/ chosen' = chosen )
  PROOF
  <2>1. ASSUME Consistency /\ Consistency' /\ [Next]_<<votes, maxBal>>
        PROVE  ( ( /\ chosen = {}
                   /\ \E v \in Value : chosen' = {v} )
                 \/ chosen' = chosen )
    PROOF
    <3>1. CASE <<votes, maxBal>>' = <<votes, maxBal>>
      PROOF
      <4>1. votes' = votes
        BY <3>1
      <4>2. chosen' = chosen
        BY <4>1 DEF chosen, ChosenAt, VotedFor
      <4> QED BY <4>2
    <3>2. CASE Next
      PROOF
      <4>1. chosen \subseteq chosen'
        BY <1>4, <3>2
      <4>2. (chosen = {}) \/ (\E v \in Value : chosen = {v})
        BY <2>1 DEF Consistency
      <4>3. (chosen' = {}) \/ (\E v \in Value : chosen' = {v})
        BY <2>1 DEF Consistency
      <4>4. CASE chosen = {}
        PROOF
        <5>1. CASE chosen' = {}
          BY <4>4, <5>1
        <5>2. CASE \E v \in Value : chosen' = {v}
          BY <4>4, <5>2
        <5> QED BY <4>3, <5>1, <5>2
      <4>5. CASE \E v \in Value : chosen = {v}
        PROOF
        <5>1. PICK v \in Value : chosen = {v}
          BY <4>5
        <5>2. CASE chosen' = {}
          BY <4>1, <5>1, <5>2, SMT
        <5>3. CASE \E w \in Value : chosen' = {w}
          PROOF
          <6>1. PICK w \in Value : chosen' = {w}
            BY <5>3
          <6>2. chosen' = chosen
            BY <4>1, <5>1, <6>1, SMT
          <6> QED BY <6>2
        <5> QED BY <4>3, <5>2, <5>3
      <4> QED BY <4>2, <4>4, <4>5
    <3> QED BY <2>1, <3>1, <3>2
  <2> QED BY <2>1
<1>6. Spec => []Consistency
  BY Consistent
<1>7. Spec => chosen = {}
  BY <1>1 DEF Spec
<1>8. Consistency /\ Consistency' /\ [Next]_<<votes, maxBal>> => [C!Next]_chosen
  BY <1>5 DEF C!Next
<1>9. Spec => [][C!Next]_chosen
  BY <1>8, <1>6, PTL DEF Spec
<1>10. Spec => C!Spec
  BY <1>7, <1>9 DEF C!Spec, C!Init
<1> QED BY <1>10

=============================================================================
