------------------------------- MODULE Voting_Invariant -------------------------------
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
PROOF
  <1>1. Init => Inv
    BY DEF Init, Inv, TypeOK, VotesSafe, OneValuePerBallot,
           VotedFor, SafeAt, Ballot
  <1>2. Inv /\ [Next]_<<votes, maxBal>> => Inv'
  PROOF
    <2>1. ASSUME Inv, [Next]_<<votes, maxBal>>
           PROVE Inv'
    PROOF
      <3>1. CASE Next
      PROOF
        <4>1. TypeOK'
          BY <2>1, SMT DEF Inv, Next, IncreaseMaxBal, VoteFor, TypeOK, Ballot, VotedFor
        <4>2. VotesSafe'
        PROOF
          <5> SUFFICES ASSUME NEW aa \in Acceptor,
                                NEW bb \in Ballot,
                                NEW vv \in Value,
                                VotedFor(aa, bb, vv)'
                         PROVE  SafeAt(bb, vv)'
            BY DEF VotesSafe
          <5>1. CASE VotedFor(aa, bb, vv)
          PROOF
            <6>1. SafeAt(bb, vv)
              BY <2>1, <5>1 DEF Inv, VotesSafe
            <6> QED
              BY <2>1, <3>1, <4>1, <6>1, SafeAtStable DEF Inv
          <5>2. CASE ~ VotedFor(aa, bb, vv)
          PROOF
            <6>1. PICK a \in Acceptor, b \in Ballot :
                    \/ IncreaseMaxBal(a, b)
                    \/ \E v \in Value : VoteFor(a, b, v)
              BY <3>1 DEF Next
            <6>2. CASE IncreaseMaxBal(a, b)
              BY <5>1, <5>2, <6>2 DEF IncreaseMaxBal, VotedFor
            <6>3. CASE \E v \in Value : VoteFor(a, b, v)
            PROOF
              <7>1. PICK v \in Value : VoteFor(a, b, v)
                BY <6>3
              <7>2. aa = a /\ bb = b /\ vv = v
                BY <5>1, <5>2, <7>1, SMT DEF VoteFor, VotedFor
              <7>3. PICK Q \in Quorum : ShowsSafeAt(Q, b, v)
                BY <7>1 DEF VoteFor
              <7>4. SafeAt(b, v)
                BY <2>1, <7>3, ShowsSafety DEF Inv
              <7>5. SafeAt(b, v)'
                BY <2>1, <3>1, <4>1, <7>4, SafeAtStable DEF Inv
              <7> QED BY <7>2, <7>5
            <6> QED BY <6>1, <6>2, <6>3
          <5> QED BY <5>1, <5>2
        <4>3. OneValuePerBallot'
          BY <2>1 DEF Next, IncreaseMaxBal, VoteFor, Inv,
             OneValuePerBallot, VotedFor, TypeOK, Ballot
        <4> QED BY <4>1, <4>2, <4>3 DEF Inv
      <3>2. CASE UNCHANGED <<votes, maxBal>>
      PROOF
        <4>1. votes' = votes /\ maxBal' = maxBal
          BY <3>2
        <4>2. TypeOK'
          BY <2>1, <4>1 DEF Inv, TypeOK
        <4>3. VotesSafe'
          BY <2>1, <4>1 DEF Inv, VotesSafe, VotedFor, SafeAt,
             NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt
        <4>4. OneValuePerBallot'
          BY <2>1, <4>1 DEF Inv, OneValuePerBallot, VotedFor
        <4> QED BY <4>2, <4>3, <4>4 DEF Inv
      <3> QED BY <2>1, <3>1, <3>2, SMT DEF Inv
    <2> QED BY <2>1
  <1> QED BY <1>1, <1>2, PTL DEF Spec

=============================================================================
