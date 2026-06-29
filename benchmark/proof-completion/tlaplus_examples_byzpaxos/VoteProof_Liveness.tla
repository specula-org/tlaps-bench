----------------------------- MODULE VoteProof_Liveness ------------------------------
(***************************************************************************)
(* This is a high-level consensus algorithm in which a set of processes    *)
(* called `acceptors' cooperatively choose a value.  The algorithm uses    *)
(* numbered ballots, where a ballot is a round of voting.  Acceptors cast  *)
(* votes in ballots, casting at most one vote per ballot.  A value is      *)
(* chosen when a large enough set of acceptors, called a `quorum', have    *)
(* all voted for the same value in the same ballot.                        *)
(*                                                                         *)
(* Ballots are not executed in order.  Different acceptors may be          *)
(* concurrently performing actions for different ballots.                  *)
(***************************************************************************)
EXTENDS Integers, NaturalsInduction, FiniteSets, FiniteSetTheorems, 
        WellFoundedInduction, TLC, TLAPS

CONSTANT Value,     \* As in module Consensus, the set of choosable values.
         Acceptor,  \* The set of all acceptors.
         Quorum     \* The set of all quorums.
 
(***************************************************************************)
(* The following assumption asserts that a quorum is a set of acceptors,   *)
(* and the fundamental assumption we make about quorums: any two quorums   *)
(* have a non-empty intersection.                                          *)
(***************************************************************************)
ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF OMITTED
(***************************************************************************)
(* Ballot is the set of all ballot numbers.  For simplicity, we let it be  *)
(* the set of natural numbers.  However, we write Ballot for that set to   *)
(* make it clear what the function of those natural numbers are.           *)
(*                                                                         *)
(* The algorithm and its refinements work with Ballot any set with minimal *)
(* element 0, -1 not an element of Ballot, and a well-founded total order  *)
(* < on Ballot \cup {-1} with minimal element -1, and 0 < b for all        *)
(* non-zero b in Ballot.  In the proof, any set of the form i..j must be   *)
(* replaced by the set of all elements b in Ballot \cup {-1} with i \leq b *)
(* \leq j, and i..(j-1) by the set of such b with i \leq b < j.            *)
(***************************************************************************)
Ballot == Nat
(***************************************************************************)
(* In the algorithm, each acceptor can cast one or more votes, where each  *)
(* vote cast by an acceptor has the form <<b, v>> indicating that the      *)
(* acceptor has voted for value v in ballot b.  A value is chosen if a     *)
(* quorum of acceptors have voted for it in the same ballot.               *)
(*                                                                         *)
(* The algorithm uses two variables, `votes' and `maxBal', both arrays     *)
(* indexed by acceptor.  Their meanings are:                               *)
(*                                                                         *)
(*   votes[a] - The set of votes cast by acceptor `a'.                     *)
(*                                                                         *)
(*   maxBal[a] - The number of the highest-numbered ballot in which `a'    *)
(*               has cast a vote, or -1 if it has not yet voted.           *)
(*                                                                         *)
(* The algorithm does not let acceptor `a' vote in any ballot less than    *)
(* maxBal[a].                                                              *)
(*                                                                         *)
(* We specify our algorithm by the following PlusCal algorithm.  The       *)
(* specification Spec defined by this algorithm describes only the safety  *)
(* properties of the algorithm.  In other words, it specifies what steps   *)
(* the algorithm may take.  It does not require that any (non-stuttering)  *)
(* steps be taken.  We prove that this specification Spec implements the   *)
(* specification Spec of module Consensus under a refinement mapping       *)
(* defined below.  This shows that the safety properties of the voting     *)
(* algorithm (and hence the algorithm with additional liveness             *)
(* requirements) imply the safety properties of the Consensus              *)
(* specification.  Liveness is discussed later.                            *)
(***************************************************************************)
 
(***************************
--algorithm Voting {
  variables votes = [a \in Acceptor |-> {}],
            maxBal = [a \in Acceptor |-> -1];
  define {
   (************************************************************************)
   (* We now define the operator SafeAt so SafeAt(b, v) is function of the *)
   (* state that equals TRUE if no value other than v has been chosen or   *)
   (* can ever be chosen in the future (because the values of the          *)
   (* variables votes and maxBal are such that the algorithm does not      *)
   (* allow enough acceptors to vote for it).  We say that value v is safe *)
   (* at ballot number b iff Safe(b, v) is true.  We define Safe in terms  *)
   (* of the following two operators.                                      *)
   (*                                                                      *)
   (* Note: This definition is weaker than would be necessary to allow a   *)
   (* refinement of ordinary Paxos consensus, since it allows different    *)
   (* quorums to "cooperate" in determining safety at b.  This is used in  *)
   (* algorithms like Vertical Paxos that are designed to allow            *)
   (* reconfiguration within a single consensus instance, but not in       *)
   (* ordinary Paxos.  See                                                 *)
   (*                                                                      *)
   (*    AUTHOR    = "Leslie Lamport and Dahlia Malkhi and Lidong Zhou ",  *)
   (*    TITLE     = "Vertical Paxos and Primary-Backup Replication",      *)
   (*    Journal   = "ACM SIGACT News (Distributed Computing Column)",     *)
   (*    editor    = {Srikanta Tirthapura and Lorenzo Alvisi},             *)
   (*    booktitle = {PODC},                                               *)
   (*    publisher = {ACM},                                                *)
   (*    YEAR = 2009,                                                      *)
   (*    PAGES = "312--313"                                                *)
   (************************************************************************)
   VotedFor(a, b, v) == <<b, v>> \in votes[a]
     (**********************************************************************)
     (* True iff acceptor a has voted for v in ballot b.                   *)
     (**********************************************************************)
   DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

   (************************************************************************)
   (* We now define SafeAt.  We define it recursively.  The nicest         *)
   (* definition is                                                        *)
   (*                                                                      *)
   (*    RECURSIVE SafeAt(_, _)                                            *)
   (*    SafeAt(b, v) ==                                                   *)
   (*      \/ b = 0                                                        *)
   (*      \/ \E Q \in Quorum :                                            *)
   (*           /\ \A a \in Q : maxBal[a] \geq b                           *)
   (*           /\ \E c \in -1..(b-1) :                                    *)
   (*                /\ (c # -1) => /\ SafeAt(c, v)                        *)
   (*                               /\ \A a \in Q :                        *)
   (*                                    \A w \in Value :                  *)
   (*                                        VotedFor(a, c, w) => (w = v)  *)
   (*          /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)      *)
   (*                                                                      *)
   (* However, TLAPS does not currently support recursive operator         *)
   (* definitions.  We therefore define it as follows using a recursive    *)
   (* function definition.                                                 *)
   (************************************************************************)
   SafeAt(b, v) ==
     LET SA[bb \in Ballot] ==
           (****************************************************************)
           (* This recursively defines SA[bb] to equal SafeAt(bb, v).      *)
           (****************************************************************)
           \/ bb = 0
           \/ \E Q \in Quorum :
                /\ \A a \in Q : maxBal[a] \geq bb
                /\ \E c \in -1..(bb-1) :
                     /\ (c # -1) => /\ SA[c]
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, c, w) => (w = v)
                     /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
     IN  SA[b]
    }
  (*************************************************************************)
  (* There are two possible actions that an acceptor can perform, each     *)
  (* defined by a macro.  In these macros, `self' is the acceptor that is  *)
  (* to perform the action.  The first action, IncreaseMaxBal(b) allows    *)
  (* acceptor `self' to set maxBal[self] to b if b is greater than the     *)
  (* current value of maxBal[self].                                        *)
  (*************************************************************************)
  macro IncreaseMaxBal(b) {
    when b > maxBal[self] ;
    maxBal[self] := b
    }
    
  (*************************************************************************)
  (* Action VoteFor(b, v) allows acceptor `self' to vote for value v in    *)
  (* ballot b if its `when' condition is satisfied.                        *)
  (*************************************************************************)
  macro VoteFor(b, v) {
    when /\ maxBal[self] \leq b
         /\ DidNotVoteIn(self, b)
         /\ \A p \in Acceptor \ {self} : 
               \A w \in Value : VotedFor(p, b, w) => (w = v)
         /\ SafeAt(b, v) ;
    votes[self]  := votes[self] \cup {<<b, v>>};
    maxBal[self] := b 
    }
    
  (*************************************************************************)
  (* The following process declaration asserts that every process `self'   *)
  (* in the set Acceptor executes its body, which loops forever            *)
  (* nondeterministically choosing a Ballot b and executing either an      *)
  (* IncreaseMaxBal(b) action or nondeterministically choosing a value v   *)
  (* and executing a VoteFor(b, v) action.  The single label indicates     *)
  (* that an entire execution of the body of the `while' loop is performed *)
  (* as a single atomic action.                                            *)
  (*                                                                       *)
  (* From this intuitive description of the process declaration, one might *)
  (* think that a process could be deadlocked by choosing a ballot b in    *)
  (* which neither an IncreaseMaxBal(b) action nor any VoteFor(b, v)       *)
  (* action is enabled.  An examination of the TLA+ translation (and an    *)
  (* elementary knowledge of the meaning of existential quantification)    *)
  (* shows that this is not the case.  You can think of all possible       *)
  (* choices of b and of v being examined simultaneously, and one of the   *)
  (* choices for which a step is possible being made.                      *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc : while (TRUE) {
           with (b \in Ballot) {
             either IncreaseMaxBal(b)
             or     with (v \in Value) { VoteFor(b, v) }
       }
     }
    }
}

The following is the TLA+ specification produced by the translation.
Blank lines, produced by the translation because of the comments, have
been deleted.
****************************)
\* BEGIN TRANSLATION
VARIABLES votes, maxBal

(* define statement *)
VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

SafeAt(b, v) ==
  LET SA[bb \in Ballot] ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
  IN  SA[b]

vars == << votes, maxBal >>

ProcSet == (Acceptor)

Init == (* Global variables *)
        /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

acceptor(self) == \E b \in Ballot:
                    \/ /\ b > maxBal[self]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ UNCHANGED votes
                    \/ /\ \E v \in Value:
                            /\ /\ maxBal[self] \leq b
                               /\ DidNotVoteIn(self, b)
                               /\ \A p \in Acceptor \ {self} :
                                     \A w \in Value : VotedFor(p, b, w) => (w = v)
                               /\ SafeAt(b, v)
                            /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]

Next == (\E self \in Acceptor: acceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
(***************************************************************************)
(* To reason about a recursively-defined operator, one must prove a        *)
(* theorem about it.  In particular, to reason about SafeAt, we need to    *)
(* prove that SafeAt(b, v) equals the right-hand side of its definition,   *)
(* for b \in Ballot and v \in Value.  This is not automatically true for a *)
(* recursive definition.  For example, from the recursive definition       *)
(*                                                                         *)
(*   Silly[n \in Nat] == CHOOSE v : v # Silly[n]                           *)
(*                                                                         *)
(* we cannot deduce that                                                   *)
(*                                                                         *)
(*   Silly[42] = CHOOSE v : v # Silly[42]                                  *)
(*                                                                         *)
(* (From that, we could easily deduce Silly[42] # Silly[42].)              *)
(***************************************************************************)

(***************************************************************************)
(* Here is the theorem that essentially asserts that SafeAt(b, v) equals   *)
(* the right-hand side of its definition.                                  *)
(***************************************************************************)
THEOREM SafeAtProp ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v) <=>
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w) => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
PROOF OMITTED

(***************************************************************************)
(* We now define TypeOK to be the type-correctness invariant.              *)
(***************************************************************************)
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

(***************************************************************************)
(* We now define `chosen' to be the state function so that the algorithm   *)
(* specified by formula Spec conjoined with the liveness requirements      *)
(* described below implements the algorithm of module Consensus (satisfies *)
(* the specification LiveSpec of that module) under a refinement mapping   *)
(* that substitutes this state function `chosen' for the variable `chosen' *)
(* of module Consensus.  The definition uses the following one, which      *)
(* defines ChosenIn(b, v) to be true iff a quorum of acceptors have all    *)
(* voted for v in ballot b.                                                *)
(***************************************************************************)
ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}
(***************************************************************************)
(* The following lemma is used for reasoning about the operator SafeAt.    *)
(* It is proved from SafeAtProp by induction.                              *)
(***************************************************************************)
LEMMA SafeLemma == 
       TypeOK => 
         \A b \in Ballot :
           \A v \in Value :
              SafeAt(b, v) => 
                \A c \in 0..(b-1) :
                  \E Q \in Quorum :
                    \A a \in Q : /\ maxBal[a] >= c
                                 /\ \/ DidNotVoteIn(a, c)
                                    \/ VotedFor(a, c, v)
PROOF OMITTED
(***************************************************************************)
(* We now define the invariant that is used to prove the correctness of    *)
(* our algorithm--meaning that specification Spec implements specification *)
(* Spec of module Consensus under our refinement mapping.  Correctness of  *)
(* the voting algorithm follows from the the following three invariants:   *)
(*                                                                         *)
(*   VInv1: In any ballot, an acceptor can vote for at most one value.     *)
(*                                                                         *)
(*   VInv2: An acceptor can vote for a value v in ballot b iff v is        *)
(*          safe at b.                                                     *)
(*                                                                         *)
(*   VInv3: Two different acceptors cannot vote for different values in    *)
(*          the same ballot.                                               *)
(*                                                                         *)
(* Their precise definitions are as follows.                               *)
(***************************************************************************)
VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
           VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
                  VotedFor(a, b, v) => SafeAt(b, v)

VInv3 ==  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
                VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

(***************************************************************************)
(* It is obvious, that VInv3 implies VInv1--a fact that we now let TLAPS   *)
(* prove as a little check that we haven't made a mistake in our           *)
(* definitions.  (Actually, we used TLC to check everything before         *)
(* attempting any proofs.) We define VInv1 separately because VInv3 is not *)
(* needed for proving safety, only for liveness.                           *)
(***************************************************************************)
THEOREM VInv3 => VInv1
PROOF OMITTED
(***************************************************************************)
(* The following lemma proves that SafeAt(b, v) implies that no value      *)
(* other than v can have been chosen in any ballot numbered less than b.   *)
(* The fact that it also implies that no value other than v can ever be    *)
(* chosen in the future follows from this and the fact that SafeAt(b, v)   *)
(* is stable--meaning that once it becomes true, it remains true forever.  *)
(* The stability of SafeAt(b, v) is proved as step <1>6 of theorem         *)
(* InductiveInvariance below.                                              *)
(*                                                                         *)
(* This lemma is used only in the proof of theorem VT1 below.              *)
(***************************************************************************)
LEMMA VT0 == /\ TypeOK
             /\ VInv1
             /\ VInv2
             => \A v, w \in Value, b, c \in Ballot : 
                   (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
PROOF OMITTED
 
(***************************************************************************)
(* The following theorem asserts that the invariance of TypeOK, VInv1, and *)
(* VInv2 implies that the algorithm satisfies the basic consensus property *)
(* that at most one value is chosen (at any time).  If you can prove it,   *)
(* then you understand why the Paxos consensus algorithm allows only a     *)
(* single value to be chosen.  Note that VInv3 is not needed to prove this *)
(* property.                                                               *)
(***************************************************************************)
THEOREM VT1 == /\ TypeOK 
               /\ VInv1
               /\ VInv2
               => \A v, w : 
                    (v \in chosen) /\ (w \in chosen) => (v = w)
PROOF OMITTED

(***************************************************************************)
(* The rest of the proof uses only the primed version of VT1--that is, the *)
(* theorem whose statement is VT1'.  (Remember that VT1 names the formula  *)
(* being asserted by the theorem we call VT1.) The formula VT1' asserts    *)
(* that VT1 is true in the second state of any transition (pair of         *)
(* states). We derive that theorem from VT1 by simple temporal logic, and  *)
(* similarly for VT0 and SafeAtProp.                                       *)
(***************************************************************************)
THEOREM SafeAtPropPrime ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v)' <=>
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal'[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)'
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w)' => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)'
PROOF OMITTED

LEMMA VT0Prime == 
  /\ TypeOK'
  /\ VInv1'
  /\ VInv2'
  => \A v, w \in Value, b, c \in Ballot : 
        (b > c) /\ SafeAt(b, v)' /\ ChosenIn(c, w)' => (v = w)
PROOF OMITTED

THEOREM VT1Prime == 
               /\ TypeOK' 
               /\ VInv1'
               /\ VInv2'
               => \A v, w : 
                    (v \in chosen') /\ (w \in chosen') => (v = w)
PROOF OMITTED

(***************************************************************************)
(* The invariance of VInv2 depends on SafeAt(b, v) being stable, meaning   *)
(* that once it becomes true it remains true forever.  Stability of        *)
(* SafeAt(b, v) depends on the following invariant.                        *)
(***************************************************************************)
VInv4 == \A a \in Acceptor, b \in Ballot : 
            maxBal[a] < b => DidNotVoteIn(a, b)
             
(***************************************************************************)
(* The inductive invariant that we use to prove correctness of this        *)
(* algorithm is VInv, defined as follows.                                  *)
(***************************************************************************)
VInv == TypeOK /\ VInv2 /\ VInv3 /\ VInv4
(***************************************************************************)
(* To simplify reasoning about the next-state action Next, we want to      *)
(* express it in a more convenient form.  This is done by lemma NextDef    *)
(* below, which shows that Next equals an action defined in terms of the   *)
(* following subactions.                                                   *)
(***************************************************************************)
IncreaseMaxBal(self, b) ==  
  /\ b > maxBal[self]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED votes

VoteFor(self, b, v) == 
  /\ maxBal[self] \leq b
  /\ DidNotVoteIn(self, b)
  /\ \A p \in Acceptor \ {self} :
        \A w \in Value : VotedFor(p, b, w) => (w = v)
  /\ SafeAt(b, v)
  /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]

BallotAction(self, b) ==
  \/ IncreaseMaxBal(self, b)
  \/ \E v \in Value : VoteFor(self, b, v)

(***************************************************************************)
(* When proving lemma NextDef, we were surprised to discover that it       *)
(* required the assumption that the set of acceptors is non-empty.  This   *)
(* assumption isn't necessary for safety, since if there are no acceptors  *)
(* there can be no quorums (see theorem QuorumNonEmpty above) so no value  *)
(* is ever chosen and the Consensus specification is trivially implemented *)
(* under our refinement mapping.  However, the assumption is necessary for *)
(* liveness and it allows us to lemma NextDef for the safety proof as      *)
(* well, so we assert it now.                                              *)
(***************************************************************************)
ASSUME AcceptorNonempty == Acceptor # {}

(***************************************************************************)
(* The proof of the lemma itself is quite simple.                          *)
(***************************************************************************)
LEMMA NextDef ==
  TypeOK => 
   (Next =  \E self \in Acceptor :
                 \E b \in Ballot : BallotAction(self, b) )
PROOF OMITTED
(***************************************************************************)
(* We now come to the proof that VInv is an invariant of the               *)
(* specification.  This follows from the following result, which asserts   *)
(* that it is an inductive invariant of the next-state action.  This fact  *)
(* is used in the liveness proof as well.                                  *)
(***************************************************************************)
THEOREM InductiveInvariance == VInv /\ [Next]_vars => VInv'
PROOF OMITTED

(***************************************************************************)
(* The invariance of VInv follows easily from theorem InductiveInvariance  *)
(* and the following result, which is easy to prove with TLAPS.            *)
(***************************************************************************)
THEOREM InitImpliesInv == Init => VInv
PROOF OMITTED

(***************************************************************************)
(* The following theorem asserts that VInv is an invariant of Spec.        *)
(***************************************************************************)
THEOREM VT2 == Spec => []VInv
PROOF OMITTED

(***************************************************************************)
(* The following INSTANCE statement instantiates module Consensus with the *)
(* following expressions substituted for the parameters (the CONSTANTS and *)
(* VARIABLES) of that module:                                              *)
(*                                                                         *)
(*   Parameter of Consensus    Expression (of this module)                 *)
(*   ----------------------    ---------------------------                 *)
(*    Value                     Value                                      *)
(*    chosen                    chosen                                     *)
(*                                                                         *)
(* (Note that if no substitution is specified for a parameter, the default *)
(* is to substitute the parameter or defined operator of the same name.)   *)
(* More precisely, for each defined identifier id of module Consensus,     *)
(* this statement defines C!id to equal the value of id under these        *)
(* substitutions.                                                          *)
(***************************************************************************)
C == INSTANCE Consensus 
Refines == C!Spec

(***************************************************************************)
(* The following theorem asserts that the safety properties of the voting  *)
(* algorithm (specified by formula Spec) of this module implement the      *)
(* consensus safety specification Spec of module Consensus under the       *)
(* substitution (refinement mapping) of the INSTANCE statement.            *)
(***************************************************************************)
THEOREM VT3 == Spec => C!Spec 
PROOF OMITTED

(***************************************************************************)
(*                                Liveness                                 *)
(*                                                                         *)
(* We now state the liveness property required of our voting algorithm and *)
(* prove that it and the safety property imply specification LiveSpec of   *)
(* module Consensus under our refinement mapping.                          *)
(*                                                                         *)
(* We begin by stating two additional assumptions that are necessary for   *)
(* liveness.  Liveness requires that some value eventually be chosen.      *)
(* This cannot hold with an infinite set of acceptors.  More precisely,    *)
(* liveness requires the existence of a finite quorum.  (Otherwise, it     *)
(* would be impossible for all acceptors of any quorum ever to have voted, *)
(* so no value could ever be chosen.) Moreover, it is impossible to choose *)
(* a value if there are no values.  Hence, we make the following two       *)
(* assumptions.                                                            *)
(***************************************************************************)      
ASSUME AcceptorFinite == IsFiniteSet(Acceptor)

ASSUME ValueNonempty == Value # {}

LEMMA FiniteSetHasMax ==
  ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), S # {}
  PROVE  \E max \in S : \A x \in S : max >= x
PROOF OMITTED

(***************************************************************************)
(* The following theorem implies that it is always possible to find a      *)
(* ballot number b and a value v safe at b by choosing b large enough and  *)
(* then having a quorum of acceptors perform IncreaseMaxBal(b) actions.    *)
(* It will be used in the liveness proof.  Observe that it is for          *)
(* liveness, not safety, that invariant VInv3 is required.                 *)
(***************************************************************************)
THEOREM VT4 == TypeOK /\ VInv2 /\ VInv3  =>
                \A Q \in Quorum, b \in Ballot :
                   (\A a \in Q : (maxBal[a] >= b)) => \E v \in Value : SafeAt(b,v)
\* Checked as an invariant by TLC with 3 acceptors, 3 ballots, 2 values
PROOF OMITTED
(***************************************************************************)
(* The progress property we require of the algorithm is that a quorum of   *)
(* acceptors, by themselves, can eventually choose a value v.  This means  *)
(* that, for some quorum Q and ballot b, the acceptors `a' of Q must make  *)
(* SafeAt(b, v) true by executing IncreaseMaxBal(a, b) and then must       *)
(* execute VoteFor(a, b, v) to choose v.  In order to be able to execute   *)
(* VoteFor(a, b, v), acceptor `a' must not execute a Ballot(a, c) action   *)
(* for any c > b.                                                          *)
(*                                                                         *)
(* These considerations lead to the following liveness requirement         *)
(* LiveAssumption.  The WF condition ensures that the acceptors `a' in Q   *)
(* eventually execute the necessary BallotAction(a, b) actions if they are *)
(* enabled, and the [][...]_vars condition ensures that they never perform *)
(* BallotAction actions for higher-numbered ballots, so the necessary      *)
(* BallotAction(a, b) actions are enabled.                                 *)
(***************************************************************************)
LiveAssumption ==
  \E Q \in Quorum, b \in Ballot :
     /\ \A self \in Q : WF_vars(BallotAction(self, b))
     /\ [] [\A self \in Q : \A c \in Ballot : 
               (c > b) => ~ BallotAction(self, c)]_vars
     
LiveSpec == Spec /\ LiveAssumption  
(***************************************************************************)
(* LiveAssumption is stronger than necessary.  Instead of requiring that   *)
(* an acceptor in Q never executes an action of a higher-numbered ballot   *)
(* than b, it suffices that it doesn't execute such an action until unless *)
(* it has voted in ballot b.  However, the natural liveness requirement    *)
(* for a Paxos consensus algorithm implies condition LiveAssumption.       *)
(*                                                                         *)
(* Condition LiveAssumption is a liveness property, constraining only what *)
(* eventually happens.  It is straightforward to replace "eventually       *)
(* happens" by "happens within some length of time" and convert            *)
(* LiveAssumption into a real-time condition.  We have not done that for   *)
(* three reasons:                                                          *)
(*                                                                         *)
(*  1. The real-time requirement and, we believe, the real-time reasoning  *)
(*     will be more complicated, since temporal logic was developed to     *)
(*     abstract away much of the complexity of reasoning about explicit    *)
(*     times.                                                              *)
(*                                                                         *)
(*  2. TLAPS does not yet support reasoning about real numbers.            *)
(*                                                                         *)
(*  3. Reasoning about real-time specifications consists entirely          *)
(*     of safety reasoning, which is almost entirely action reasoning.     *)
(*     We want to see how the TLA+ proof language and TLAPS do on          *)
(*     temporal logic reasoning.                                           *)
(*                                                                         *)
(*                                                                         *)
(***************************************************************************)
(***************************************************************************)
(* Here is our proof that LiveSpec implements the specification LiveSpec   *)
(* of module Consensus under our refinement mapping.                       *)
(***************************************************************************)
THEOREM Liveness == LiveSpec => C!LiveSpec
PROOF OBVIOUS

===============================================================================
