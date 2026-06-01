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

OneVote == 
    \A a \in Acceptor, b \in Ballot, v, w \in Value : 
        VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
        VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot
-----------------------------------------------------------------------------
LEMMA InitInv == Init => Inv
  BY SMT DEF Init, Inv, TypeOK, VotesSafe, OneValuePerBallot,
             VotedFor, SafeAt

LEMMA OneValuePerBallotImpliesOneVote == OneValuePerBallot => OneVote
  BY SMT DEF OneValuePerBallot, OneVote

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
  BY SMT, QuorumAssumption DEF QuorumAssumption

LEMMA QuorumIntersection ==
  \A Q1, Q2 \in Quorum : \E a \in Acceptor : a \in Q1 /\ a \in Q2
  BY SMT, QuorumAssumption DEF QuorumAssumption

LEMMA ChosenVoteWitness ==
  \A b \in Ballot, v \in Value :
    ChosenAt(b, v) => \E a \in Acceptor : VotedFor(a, b, v)
  BY SMT, QuorumNonEmpty, QuorumAssumption DEF ChosenAt, QuorumAssumption

LEMMA ChosenSafeAt ==
  Inv =>
    \A b \in Ballot, v \in Value :
      ChosenAt(b, v) => SafeAt(b, v)
  BY SMT, ChosenVoteWitness DEF Inv, VotesSafe

LEMMA SameBallotChosenUnique ==
  OneValuePerBallot =>
    \A b \in Ballot, v1, v2 \in Value :
      ChosenAt(b, v1) /\ ChosenAt(b, v2) => v1 = v2
  BY SMT, QuorumIntersection
     DEF OneValuePerBallot, ChosenAt, VotedFor

LEMMA NoneOtherChoosableAndChosen ==
  OneValuePerBallot =>
    \A b \in Ballot, v1, v2 \in Value :
      ChosenAt(b, v1) /\ NoneOtherChoosableAt(b, v2) => v1 = v2
  BY SMT, QuorumIntersection
     DEF OneValuePerBallot, ChosenAt, NoneOtherChoosableAt,
         CannotVoteAt, DidNotVoteAt, VotedFor

LEMMA ChosenAtUnique ==
    Inv =>
      \A b1, b2 \in Ballot, v1, v2 \in Value :
        ChosenAt(b1, v1) /\ ChosenAt(b2, v2) => v1 = v2
PROOF
<1>. SUFFICES ASSUME Inv,
                      NEW b1 \in Ballot, NEW b2 \in Ballot,
                      NEW v1 \in Value, NEW v2 \in Value,
                      ChosenAt(b1, v1), ChosenAt(b2, v2)
               PROVE v1 = v2
  BY SMT
<1>1. CASE b1 = b2
  BY <1>1, SameBallotChosenUnique DEF Inv
<1>2. CASE b1 < b2
  <2>1. SafeAt(b2, v2)
    BY <1>2, ChosenSafeAt
  <2>2. b1 \in 0..(b2-1)
    BY <1>2, SMT DEF Ballot
  <2>3. NoneOtherChoosableAt(b1, v2)
    BY <2>1, <2>2 DEF SafeAt
  <2> QED
    BY <2>3, NoneOtherChoosableAndChosen DEF Inv
<1>3. CASE b2 < b1
  <2>1. SafeAt(b1, v1)
    BY <1>3, ChosenSafeAt
  <2>2. b2 \in 0..(b1-1)
    BY <1>3, SMT DEF Ballot
  <2>3. NoneOtherChoosableAt(b2, v1)
    BY <2>1, <2>2 DEF SafeAt
  <2> QED
    BY <2>3, NoneOtherChoosableAndChosen DEF Inv
<1>4. QED
  BY <1>1, <1>2, <1>3, SMT DEF Ballot

LEMMA InvImpliesConsistency == Inv => Consistency
PROOF
<1>. SUFFICES ASSUME Inv PROVE Consistency
  BY SMT
<1>1. CASE chosen = {}
  BY <1>1 DEF Consistency
<1>2. CASE chosen # {}
  <2>1. PICK v \in chosen : TRUE
    BY <1>2
  <2>2. v \in Value /\ \E b \in Ballot : ChosenAt(b, v)
    BY <2>1 DEF chosen
  <2>3. chosen = {v}
    PROOF
    <3>1. \A x : x \in chosen => x \in {v}
      PROOF
      <4>. SUFFICES ASSUME NEW x, x \in chosen PROVE x \in {v}
        BY SMT
      <4>1. x \in Value /\ \E b \in Ballot : ChosenAt(b, x)
        BY DEF chosen
      <4>2. PICK bx \in Ballot : ChosenAt(bx, x)
        BY <4>1
      <4>3. PICK bv \in Ballot : ChosenAt(bv, v)
        BY <2>2
      <4>4. x = v
        BY <4>1, <4>2, <4>3, <2>2, ChosenAtUnique
      <4> QED
        BY <4>4
      <3>2. \A x : x \in {v} => x \in chosen
        BY <2>1
      <3>3. \A x : x \in chosen <=> x \in {v}
        BY <3>1, <3>2
      <3> QED
        BY <3>3, SetExtensionality
    <2> QED
      BY <2>2, <2>3 DEF Consistency
<1>3. QED
  BY <1>1, <1>2

-----------------------------------------------------------------------------
LEMMA TypeOKNext == TypeOK /\ Next => TypeOK'
  BY SMT DEF TypeOK, Next, IncreaseMaxBal, VoteFor, Ballot

LEMMA ExceptOther ==
  ASSUME NEW S, NEW T, NEW f \in [S -> T],
         NEW i \in S, NEW j \in S, NEW e, j # i
  PROVE  [f EXCEPT ![i] = e][j] = f[j]
  OBVIOUS

LEMMA ExceptSame ==
  ASSUME NEW S, NEW T, NEW f \in [S -> T], NEW i \in S, NEW e
  PROVE  [f EXCEPT ![i] = e][i] = e
  OBVIOUS

LEMMA VotesMonotonic ==
  TypeOK /\ Next =>
    \A a \in Acceptor : votes[a] \subseteq votes'[a]
  BY SMT DEF TypeOK, Next, IncreaseMaxBal, VoteFor

LEMMA MaxBalMonotonic ==
  TypeOK /\ Next =>
    \A a \in Acceptor : maxBal'[a] >= maxBal[a]
  BY SMT DEF TypeOK, Next, IncreaseMaxBal, VoteFor, Ballot

LEMMA CannotVoteAtStable ==
  TypeOK /\ Next =>
    \A a \in Acceptor, b \in Ballot :
      CannotVoteAt(a, b) => CannotVoteAt(a, b)'
  BY SMT DEF TypeOK, Next, IncreaseMaxBal, VoteFor, CannotVoteAt,
             DidNotVoteAt, VotedFor, Ballot

LEMMA OneValuePerBallotNext ==
  TypeOK /\ OneValuePerBallot /\ Next => OneValuePerBallot'
  BY SMT DEF TypeOK, OneValuePerBallot, Next, IncreaseMaxBal, VoteFor,
             VotedFor, Ballot

LEMMA MaxVotePreventsOtherAt ==
  Inv =>
    \A Q \in Quorum, b \in Ballot, v \in Value :
      \A c \in 0..(b-1) :
        /\ \A a \in Q : maxBal[a] >= b
        /\ \E a \in Q : VotedFor(a, c, v)
        => NoneOtherChoosableAt(c, v)
PROOF
<1>. SUFFICES ASSUME Inv,
                      NEW Q \in Quorum, NEW b \in Ballot,
                      NEW v \in Value, NEW c \in 0..(b-1),
                      \A a \in Q : maxBal[a] >= b,
                      \E a \in Q : VotedFor(a, c, v)
               PROVE NoneOtherChoosableAt(c, v)
  BY SMT
<1>1. PICK av \in Q : VotedFor(av, c, v)
  BY SMT
<1>2. av \in Acceptor
  BY <1>1, QuorumAssumption DEF QuorumAssumption
<1>3. \A a \in Q : VotedFor(a, c, v) \/ CannotVoteAt(a, c)
  PROOF
  <2>. SUFFICES ASSUME NEW a \in Q
                 PROVE VotedFor(a, c, v) \/ CannotVoteAt(a, c)
    BY SMT
  <2>1. a \in Acceptor
    BY QuorumAssumption DEF QuorumAssumption
  <2>2. CASE VotedFor(a, c, v)
    BY <2>2
  <2>3. CASE ~ VotedFor(a, c, v)
    <3>1. maxBal[a] > c
      BY <2>1, <2>3, SMT, SimpleArithmetic DEF Inv, TypeOK, Ballot
    <3>2. DidNotVoteAt(a, c)
      PROOF
      <4>. SUFFICES ASSUME NEW w \in Value, VotedFor(a, c, w)
                     PROVE FALSE
        BY SMT DEF DidNotVoteAt
      <4>1. w = v
        BY <1>1, <1>2, <2>1, <2>3, SMT
           DEF Inv, OneValuePerBallot, Ballot
      <4> QED
        BY <2>3, <4>1
      <3> QED
        BY <3>1, <3>2 DEF CannotVoteAt
  <2>4. QED
    BY <2>2, <2>3
<1>4. QED
  BY <1>3 DEF NoneOtherChoosableAt

LEMMA ShowsSafety ==
  Inv =>
    \A Q \in Quorum, b \in Ballot, v \in Value :
      ShowsSafeAt(Q, b, v) => SafeAt(b, v)
PROOF
<1>. SUFFICES ASSUME Inv,
                      NEW Q \in Quorum, NEW b \in Ballot,
                      NEW v \in Value, ShowsSafeAt(Q, b, v)
               PROVE SafeAt(b, v)
  BY SMT
<1>1. PICK c \in -1..(b-1) :
          /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
          /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
  BY DEF ShowsSafeAt
<1>2. \A a \in Q : maxBal[a] >= b
  BY DEF ShowsSafeAt
<1>3. \A d \in 0..(b-1) : NoneOtherChoosableAt(d, v)
  PROOF
  <2>. SUFFICES ASSUME NEW d \in 0..(b-1)
                 PROVE NoneOtherChoosableAt(d, v)
    BY SMT
  <2>1. CASE d < c
    <3>1. c # -1
      BY <2>1, SMT, SimpleArithmetic
    <3>2. c \in Ballot
      BY <2>1, <3>1, SMT DEF Ballot
    <3>3. PICK ac \in Q : VotedFor(ac, c, v)
      BY <1>1, <3>1
    <3>4. ac \in Acceptor
      BY <3>3, QuorumAssumption DEF QuorumAssumption
    <3>5. SafeAt(c, v)
      BY <3>2, <3>3, <3>4 DEF Inv, VotesSafe
    <3>6. d \in 0..(c-1)
      BY <2>1, SMT, SimpleArithmetic DEF Ballot
    <3> QED
      BY <3>5, <3>6 DEF SafeAt
  <2>2. CASE d = c
    <3>1. c \in 0..(b-1)
      BY <2>2
    <3>2. PICK ac \in Q : VotedFor(ac, c, v)
      BY <1>1, <2>2, SMT
    <3>3. NoneOtherChoosableAt(c, v)
      BY <1>2, <3>1, <3>2, MaxVotePreventsOtherAt
    <3> QED
      BY <2>2, <3>3
  <2>3. CASE c < d
    <3>1. d \in (c+1)..(b-1)
      BY <2>3, SMT, SimpleArithmetic DEF Ballot
    <3>2. b > d
      BY <3>1, SMT, SimpleArithmetic DEF Ballot
    <3>3. \A a \in Q : maxBal[a] > d
      PROOF
      <4>. SUFFICES ASSUME NEW a \in Q PROVE maxBal[a] > d
        BY SMT
      <4>1. maxBal[a] >= b
        BY <1>2
      <4>2. a \in Acceptor
        BY QuorumAssumption DEF QuorumAssumption
      <4>3. maxBal[a] \in Ballot \cup {-1}
        BY <4>2 DEF Inv, TypeOK
      <4> QED
        BY <3>2, <4>1, <4>3, SMT, SimpleArithmetic DEF Ballot
    <3>4. \A a \in Q : DidNotVoteAt(a, d)
      BY <1>1, <3>1
    <3>5. \A a \in Q : CannotVoteAt(a, d)
      BY <3>3, <3>4 DEF CannotVoteAt
    <3> QED
      BY <3>5 DEF NoneOtherChoosableAt
  <2>4. QED
    BY <2>1, <2>2, <2>3, SMT, SimpleArithmetic
<1>4. QED
  BY <1>3 DEF SafeAt

LEMMA SafeAtStable ==
  Inv /\ Next /\ TypeOK' =>
    \A b \in Ballot, v \in Value :
      SafeAt(b, v) => SafeAt(b, v)'
PROOF
<1>. SUFFICES ASSUME Inv, Next, TypeOK',
                      NEW b \in Ballot, NEW v \in Value, SafeAt(b, v)
               PROVE SafeAt(b, v)'
  BY SMT
<1>0. TypeOK
  BY DEF Inv
<1>1. \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)'
  PROOF
  <2>. SUFFICES ASSUME NEW c \in 0..(b-1)
                 PROVE NoneOtherChoosableAt(c, v)'
    BY SMT
  <2>1. c \in Ballot
    BY SMT DEF Ballot
  <2>2. NoneOtherChoosableAt(c, v)
    BY DEF SafeAt
  <2>3. PICK Q \in Quorum :
          \A a \in Q : VotedFor(a, c, v) \/ CannotVoteAt(a, c)
    BY <2>2 DEF NoneOtherChoosableAt
  <2>4. \A a \in Q : VotedFor(a, c, v)' \/ CannotVoteAt(a, c)'
    PROOF
    <3>. SUFFICES ASSUME NEW a \in Q
                   PROVE VotedFor(a, c, v)' \/ CannotVoteAt(a, c)'
      BY SMT
    <3>1. a \in Acceptor
      BY QuorumAssumption DEF QuorumAssumption
    <3>2. CASE VotedFor(a, c, v)
      <4>1. votes[a] \subseteq votes'[a]
        BY <1>0, <3>1, VotesMonotonic
      <4>2. VotedFor(a, c, v)'
        BY <3>2, <4>1 DEF VotedFor
      <4> QED
        BY <4>2
    <3>3. CASE CannotVoteAt(a, c)
      <4>1. CannotVoteAt(a, c)'
        BY <1>0, <2>1, <3>1, <3>3, CannotVoteAtStable
      <4> QED
        BY <4>1
    <3>4. QED
      BY <2>3, <3>2, <3>3
  <2>5. QED
    BY <2>3, <2>4 DEF NoneOtherChoosableAt
<1>2. QED
  BY <1>1 DEF SafeAt

LEMMA VoteForActionSafe ==
  Inv /\ Next /\ TypeOK' =>
    \A a \in Acceptor, b \in Ballot, v \in Value :
      VoteFor(a, b, v) => SafeAt(b, v)'
  BY SMT, ShowsSafety, SafeAtStable DEF VoteFor, Inv

LEMMA NewVoteFromVoteForSafe ==
  Inv /\ Next /\ TypeOK' =>
    \A aa \in Acceptor, bb \in Ballot, vv \in Value :
      \A a \in Acceptor, b \in Ballot, v \in Value :
        VoteFor(aa, bb, vv) /\ VotedFor(a, b, v)' /\ ~ VotedFor(a, b, v)
        => SafeAt(b, v)'
PROOF
<1>. SUFFICES ASSUME Inv, Next, TypeOK',
                      NEW aa \in Acceptor, NEW bb \in Ballot,
                      NEW vv \in Value, NEW a \in Acceptor,
                      NEW b \in Ballot, NEW v \in Value,
                      VoteFor(aa, bb, vv),
                      VotedFor(a, b, v)',
                      ~ VotedFor(a, b, v)
               PROVE SafeAt(b, v)'
  BY SMT
<1>1. votes' = [votes EXCEPT ![aa] = votes[aa] \cup {<<bb, vv>>}]
  BY DEF VoteFor
<1>1a. votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  BY DEF Inv, TypeOK
<1>2. a = aa
  PROOF
  <2>. SUFFICES ASSUME a # aa PROVE FALSE
    BY SMT
  <2>1. votes'[a] = votes[a]
    BY <1>1, <1>1a, ExceptOther
  <2> QED
    BY <2>1 DEF VotedFor
<1>3. votes'[aa] = votes[aa] \cup {<<bb, vv>>}
  BY <1>1, <1>1a, ExceptSame
<1>4. <<b, v>> \in votes'[aa]
  BY <1>2 DEF VotedFor
<1>5. <<b, v>> \in votes[aa] \cup {<<bb, vv>>}
  BY <1>3, <1>4
<1>6. <<b, v>> \notin votes[aa]
  BY <1>2 DEF VotedFor
<1>7. <<b, v>> = <<bb, vv>>
  BY <1>5, <1>6
<1>8. b = bb /\ v = vv
  BY <1>7
<1>9. SafeAt(bb, vv)'
  BY VoteForActionSafe
<1> QED
  BY <1>8, <1>9

LEMMA NewVoteSafe ==
  Inv /\ Next /\ TypeOK' =>
    \A a \in Acceptor, b \in Ballot, v \in Value :
      VotedFor(a, b, v)' /\ ~ VotedFor(a, b, v) => SafeAt(b, v)'
  BY SMT, NewVoteFromVoteForSafe
     DEF Inv, Next, IncreaseMaxBal, VoteFor, VotedFor, Ballot

LEMMA VotesSafeNext ==
  Inv /\ Next /\ TypeOK' /\ OneValuePerBallot' => VotesSafe'
  BY SMT, SafeAtStable, NewVoteSafe
     DEF Inv, VotesSafe, Next, IncreaseMaxBal, VoteFor, VotedFor, Ballot

LEMMA InvNext == Inv /\ Next => Inv'
  BY SMT, TypeOKNext, OneValuePerBallotNext, VotesSafeNext
     DEF Inv

LEMMA InvStutter == Inv /\ UNCHANGED <<votes, maxBal>> => Inv'
  BY SMT DEF Inv, TypeOK, VotesSafe, OneValuePerBallot, VotedFor,
             SafeAt, NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt

LEMMA InvAction == Inv /\ [Next]_<<votes, maxBal>> => Inv'
  BY SMT, InvNext, InvStutter

-----------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
PROOF
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_<<votes, maxBal>> => Inv'
  BY InvAction
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
THEOREM Consistent == Spec => []Consistency
PROOF
<1>1. Spec => []Inv
  BY Invariant
<1>2. Inv => Consistency
  BY InvImpliesConsistency
<1>3. []Inv => []Consistency
  BY <1>2, PTL
<1> QED
  BY <1>1, <1>3, PTL
----------------------------------------------------------------------------

=============================================================================
