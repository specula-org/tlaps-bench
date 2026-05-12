---- MODULE PaxosProof_Refinement ----
EXTENDS FiniteSets, Integers, NaturalsInduction, TLAPS
(* ---- Content from module Sets ---- *)
  \** NB: Module NaturalsInduction comes from the TLAPS library, usually
  \** installed in /usr/local/lib/tlaps. Make sure this is in your Toolbox
  \** search path, see Preferences/TLA+ Preferences.

IsBijection(f, S, T) == /\ f \in [S -> T]
                        /\ \A x, y \in S : (x # y) => (f[x] # f[y])
                        /\ \A y \in T : \E x \in S : f[x] = y


IsFiniteSet(S) == \E n \in Nat : \E f : IsBijection(f, 1..n, S)

(****************************************************************************)
(* Finite sets and cardinality are defined in the TLA+ standard module      *)
(* FiniteSets, but this is not yet natively supported by TLAPS. For the     *)
(* time being, we use the following axiom for defining set cardinality.     *)
(****************************************************************************)
\* Cardinality(S) == CHOOSE n : (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)

CONSTANT Cardinality(_)
AXIOM CardinalityAxiom ==
         \A S : IsFiniteSet(S) =>
           \A n : (n = Cardinality(S)) <=>
                    (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
-----------------------------------------------------------------------------

THEOREM CardinalityInNat == \A S : IsFiniteSet(S) => Cardinality(S) \in Nat
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityZero ==
           /\ IsFiniteSet({})
           /\ Cardinality({}) = 0
           /\ \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
  PROOF OMITTED

THEOREM CardinalityPlusOne ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW x, x \notin S
    PROVE  /\ IsFiniteSet(S \cup {x})
           /\ Cardinality(S \cup {x}) = Cardinality(S) + 1
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityOne == \A m : /\ IsFiniteSet({m})
                                 /\ Cardinality({m}) = 1
  PROOF OMITTED

THEOREM CardinalityTwo == \A m, p : m # p => 
                              /\ IsFiniteSet({m,p})
                              /\ Cardinality({m,p}) = 2
  PROOF OMITTED

THEOREM IntervalCardinality ==  
  ASSUME NEW a \in Nat, NEW b \in Nat 
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
  PROOF OMITTED

-----------------------------------------------------------------------------

THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T, 
         IsBijection(f, S, T) 
  PROVE  \E g : IsBijection(g, T, S)
  PROOF OMITTED

THEOREM IsBijectionTransitive ==
  ASSUME NEW f1, NEW f2, NEW S, NEW T, NEW U, 
           IsBijection(f1, S, U),
           IsBijection(f2, U, T) 
  PROVE  \E g : IsBijection(g, S, T)
  PROOF OMITTED

THEOREM IsBijectionCardinality ==
  \A f, S, T : /\ IsFiniteSet(S)
               /\ IsFiniteSet(T)
               => (IsBijection(f, S, T) <=> Cardinality(S) = Cardinality(T))

LEMMA CardinalitySetMinus ==
      ASSUME NEW S, IsFiniteSet(S),
             NEW x \in S
      PROVE /\ IsFiniteSet(S \ {x})
            /\ Cardinality(S \ {x}) = Cardinality(S) - 1
  PROOF OMITTED

THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
  PROOF OMITTED

-------------------------------------------------------

THEOREM CardinalityUnion ==
          \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) =>
                      /\ IsFiniteSet(S \cup T)
                      /\ IsFiniteSet(S \cap T)
                      /\ Cardinality(S \cup T) =
                              Cardinality(S) + Cardinality(T)
                              - Cardinality(S \cap T)  

-----------------------------------------------------------------------------

THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
  PROOF OMITTED

-------------------------------------------------------

THEOREM \A S, T , f :  /\ IsFiniteSet(S)
                       /\ f \in [S -> T]
                       /\ \A y \in T : \E x \in S : y = f[x]
                       => /\ IsFiniteSet(T)
                          /\ Cardinality(T) \leq Cardinality(S)
PROOF OMITTED

THEOREM ProductFinite ==
     \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) => IsFiniteSet(S \X T)
PROOF OMITTED

THEOREM SubsetsFinite == \A S : IsFiniteSet(S) => IsFiniteSet(SUBSET S)
PROOF OMITTED

(* ---- Content from module Consensus ---- *)
-----------------------------------------------------------------------------
CONSTANT Value  \* the set of values that can be chosen
VARIABLE chosen \* the set of values that have been chosen
-----------------------------------------------------------------------------
Init == chosen = {}

Next == 
    /\ chosen = {}
    /\ \E v \in Value : chosen' = {v}

Spec == Init /\ [][Next]_chosen
-----------------------------------------------------------------------------
Inv == 
    /\ chosen \subseteq Value
    /\ IsFiniteSet(chosen)
    /\ Cardinality(chosen) \leq 1
-----------------------------------------------------------------------------
THEOREM Invariance == Spec => []Inv
  PROOF OMITTED

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

THEOREM Refinement == Spec => C!Spec
PROOF OBVIOUS

========================================