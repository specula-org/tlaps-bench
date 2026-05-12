---- MODULE BPConProof_PmaxBalLemma4 ----
EXTENDS FiniteSets, Integers, Naturals, TLAPS, TLC
(* ---- Content from module Consensus ---- *)
(***************************************************************************)
(* The consensus problem requires a set of processes to choose a single    *)
(* value.  This module specifies the problem by specifying exactly what    *)
(* the requirements are for choosing a value.                              *)
(***************************************************************************)

(***************************************************************************)
(* We let the constant parameter Value be the set of all values that can   *)
(* be chosen.                                                              *)
(***************************************************************************)
CONSTANT Value  

(****************************************************************************
We now specify the safety property of consensus as a trivial algorithm
that describes the allowed behaviors of a consensus algorithm.  It uses
the variable `chosen' to represent the set of all chosen values.  The
algorithm is trivial; it allows only behaviors that contain a single
state-change in which the variable `chosen' is changed from its initial
value {} to the value {v} for an arbitrary value v in Value.  The
algorithm itself does not specify any fairness properties, so it also
allows a behavior in which `chosen' is not changed.  We could use a
translator option to have the translation include a fairness
requirement, but we don't bother because it is easy enough to add it by
hand to the safety specification that the translator produces.

A real specification of consensus would also include additional
variables and actions.  In particular, it would have Propose actions in
which clients propose values and Learn actions in which clients learn
what value has been chosen.  It would allow only a proposed value to be
chosen.  However, the interesting part of a consensus algorithm is the
choosing of a single value.  We therefore restrict our attention to
that aspect of consensus algorithms.  In practice, given the algorithm
for choosing a value, it is obvious how to implement the Propose and
Learn actions.

For convenience, we define the macro Choose() that describes the action
of changing the value of `chosen' from {} to {v}, for a
nondeterministically chosen v in the set Value.  (There is little
reason to encapsulate such a simple action in a macro; however our
other specs are easier to read when written with such macros, so we
start using them now.) The `when' statement can be executed only when
its condition, chosen = {}, is true.  Hence, at most one Choose()
action can be performed in any execution.  The `with' statement
executes its body for a nondeterministically chosen v in Value.
Execution of this statement is enabled only if Value is
non-empty--something we do not assume at this point because it is not
required for the safety part of consensus, which is satisfied if no
value is chosen.

We put the Choose() action inside a `while' statement that loops
forever.  Of course, only a single Choose() action can be executed.
The algorithm stops after executing a Choose() action.  Technically,
the algorithm deadlocks after executing a Choose() action because
control is at a statement whose execution is never enabled.  Formally,
termination is simply deadlock that we want to happen.  We could just
as well have omitted the `while' and let the algorithm terminate.
However, adding the `while' loop makes the TLA+ representation of the
algorithm a tiny bit simpler.

--algorithm Consensus {
  variable chosen = {}; 
  macro Choose() { when chosen = {};
                   with (v \in Value) { chosen := {v} } }
   { lbl: while (TRUE) { Choose() }
   }  
}

The PlusCal translator writes the TLA+ translation of this algorithm
below.  The formula Spec is the TLA+ specification described by the
algorithm's code.  For now, you should just understand its two
subformulas Init and Next.  Formula Init is the initial predicate and
describes all possible initial states of an execution.  Formula Next is
the next-state relation; it describes the possible state changes
(changes of the values of variables), where unprimed variables
represent their values in the old state and primed variables represent
their values in the new state.
*****************************************************************************)
\***** BEGIN TRANSLATION  
VARIABLE chosen

vars == << chosen >>

Init == (* Global variables *)
        /\ chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value:
             chosen' = {v}

Spec == Init /\ [][Next]_vars

\***** END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now prove the safety property that at most one value is chosen.  We  *)
(* first define the type-correctness invariant TypeOK, and then define Inv *)
(* to be the inductive invariant that asserts TypeOK and that the          *)
(* cardinality of the set `chosen' is at most 1.  We then prove that, in   *)
(* any behavior satisfying the safety specification Spec, the invariant    *)
(* Inv is true in all states.  This means that at most one value is chosen *)
(* in any behavior.                                                        *)
(***************************************************************************)
TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen) 

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

(***************************************************************************)
(* To prove our theorem, we need the following simple results about the    *)
(* cardinality of finite sets.                                             *)
(***************************************************************************)
AXIOM EmptySetCardinality == IsFiniteSet({}) /\ Cardinality({}) = 0
AXIOM SingletonCardinality == 
          \A e : IsFiniteSet({e}) /\ (Cardinality({e}) = 1)

(***************************************************************************)
(* Whenever we add an axiom, we should check it with TLC to make sure we   *)
(* haven't made any errors.  To check axiom SingletonCardinality, we must  *)
(* replace the unbounded quantification with a bounded one.  We therefore  *)
(* let TLC check that the following formula is true.                       *)
(***************************************************************************)
SingleCardinalityTest == 
  \A e \in SUBSET {"a", "b", "c"} : IsFiniteSet({e}) /\ (Cardinality({e}) = 1)

(***************************************************************************)
(* We now prove that Inv is an invariant, meaning that it is true in every *)
(* state in every behavior.  Before trying to prove it, we should first    *)
(* use TLC to check that it is true.  It's hardly worth bothering to       *)
(* either check or prove the obvious fact that Inv is an invariant, but    *)
(* it's a nice tiny exercise.  Model checking is instantaneous when Value  *)
(* is set to any small finite set.                                         *)
(*                                                                         *)
(* To understand the following proof, you need to understand the formula   *)
(* `Spec', which equals                                                    *)
(*                                                                         *)
(*    Init /\ [][Next]_vars                                                *)
(*                                                                         *)
(* where vars is the tuple <<chosen, pc>> of all variables.  It is a       *)
(* temporal formula satisfied by a behavior iff the behavior starts in a   *)
(* state satisfying Init and such that each step (sequence of states)      *)
(* satisfies [Next]_vars, which equals                                     *)
(*                                                                         *)
(*   Next \/ (vars'=vars)                                                  *)
(*                                                                         *)
(* Thus, each step satisfies either Next (so it is a step allowed by the   *)
(* next-state relation) or it is a "stuttering step" that leaves all the   *)
(* variables unchanged.  The reason why a spec must allow stuttering steps *)
(* will become apparent when we prove that a consensus algorithm satisfies *)
(* this specification of consensus.                                        *)
(***************************************************************************)

(***************************************************************************)
(* By default, a definition is not usable in a proof.  If the a definition *)
(* should be usable in the proof of a step, meaning that the prover can    *)
(* expand the definition, then that must be explicitly indicated--usually  *)
(* in the DEF clause of a BY statement.  A DEF clause of a USE statement   *)
(* makes the definitions in it usable in the scope of that statement.  The *)
(* following USE statement makes the definition of lbl usable everywhere   *)
(* in the rest of the module.  (There is a corresponding HIDE statement    *)
(* that makes definitions unusable in its scope.)                          *)
(***************************************************************************)
\* USE DEF lbl

(***************************************************************************)
(* The following lemma asserts that Inv is an inductive invariant of the   *)
(* next-state action Next.  It is the key step in proving that Inv is an   *)
(* invariant of (true in every behavior allowed by) specification Spec.    *)
(***************************************************************************)
LEMMA InductiveInvariance ==
           Inv /\ [Next]_vars => Inv'
  PROOF OMITTED

THEOREM Invariance == Spec => []Inv 
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define LiveSpec to be the algorithm's specification with the     *)
(* added fairness condition of weak fairness of the next-state relation,   *)
(* which asserts that execution does not stop if some action is enabled.   *)
(* The temporal formula Success asserts that some value is eventually      *)
(* chosen.  Below, we prove that LiveSpec implies Success This means that, *)
(* in every behavior satisfying LiveSpec, some value is chosen.            *)
(***************************************************************************)
LiveSpec == Spec /\ WF_vars(Next)
Success == <>(chosen # {})

(***************************************************************************)
(* For liveness, we need to assume that there exists at least one value.   *)
(***************************************************************************)
ASSUME ValueNonempty == Value # {}

(***************************************************************************)
(* TLAPS does not yet reason about ENABLED.  Therefore, we must omit all   *)
(* proofs that involve ENABLED formulas.  To perform as much of the proof  *)
(* as possible, as much as possible we restrict the use of an ENABLED      *)
(* expression to a step asserting that it equals its definition.  ENABLED  *)
(* A is true of a state s iff there is a state t such that the step s -> t *)
(* satisfies A.  It follows from this semantic definition that ENABLED A   *)
(* equals the formula obtained by                                          *)
(*                                                                         *)
(*  1. Expanding all definitions of defined symbols in A until all primes  *)
(*     are priming variables.                                              *)
(*                                                                         *)
(*  2. For each primed variable, replacing every instance of that primed   *)
(*     variable by a new symbol (the same symbol for each primed           *)
(*     variable).                                                          *)
(*                                                                         *)
(*  3. Existentially quantifying over those new symbols.                   *)
(***************************************************************************)
LEMMA EnabledDef ==
        TypeOK => 
          ((ENABLED <<Next>>_vars) <=> (chosen = {}))
  PROOF OMITTED

THEOREM LiveSpec => Success
<1>1. []Inv /\ [][Next]_vars /\ WF_vars(Next) => (chosen = {} ~> chosen # {})
  <2>1. SUFFICES [][Next]_vars /\ WF_vars(Next) => ((Inv /\ chosen = {}) ~> chosen # {})
    \* OBVIOUS (* PTL *)
    PROOF OMITTED
  <2>2. (Inv /\ (chosen = {})) /\ [Next]_vars => ((Inv' /\ (chosen' = {})) \/ chosen' # {})
    BY InductiveInvariance
  <2>3. (Inv /\ (chosen = {})) /\ <<Next>>_vars => (chosen' # {})
    BY DEF Inv, Next, vars
  <2>4. (Inv /\ (chosen = {})) => ENABLED <<Next>>_vars
\*     BY EnabledDef DEF Inv
    PROOF OMITTED
  <2>5. QED
\*     BY <2>2, <2>3, <2>4, RuleWF1
    PROOF OMITTED
<1>2. (chosen = {} ~> chosen # {}) => ((chosen = {}) => <>(chosen # {}))
\*   OBVIOUS (* PTL *)
  PROOF OMITTED
<1>3. QED
\*   BY Invariance, <1>1, <1>2 DEF LiveSpec, Spec, Init, Success (* PTL *)
  PROOF OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following theorem is used in the refinement proof in module         *)
(* VoteProof.                                                              *)
(***************************************************************************)
THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
  PROOF OMITTED

-----------------------------------------------------------------------------
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

-----------------------------------------------------------------------------
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
-----------------------------------------------------------------------------
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
(* specification Spec defined by this algorithm specifies only the safety  *)
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
-----------------------------------------------------------------------------
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
(*                                                                         *)
(* To prove the desired property of SafeAt, we use the following proof     *)
(* rule.  It will eventually be in a standard module--probably in TLAPS.   *)
(* However, for now, we put it here.                                       *)
(***************************************************************************)

THEOREM RecursiveFcnOfNat ==
          ASSUME NEW Def(_,_), 
                 \A n \in Nat : 
                    \A g, h : (\A i \in 0..(n-1) : g[i] = h[i]) => (Def(g, n) = Def(h, n))
          PROVE  LET f[n \in Nat] == Def(f, n)
                 IN  f = [n \in Nat |-> Def(f, n)]
PROOF OMITTED

(***************************************************************************)
(* Here is the theorem that essentially asserts that SafeAt(b, v) equals   *)
(* the right-hand side of its definition.                                  *)
(***************************************************************************)
THEOREM SafeAtProp ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v) =
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

-----------------------------------------------------------------------------

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
-----------------------------------------------------------------------------
(***************************************************************************)
(*                         Mathematical Induction                          *)
(*                                                                         *)
(* The following axiom asserts the validity of a standard proof by         *)
(* mathematical induction.  Some such axiom should be included in the      *)
(* standard TLAPS module.  However, instead of a rule expressed it in      *)
(* terms of a function f, it would be more convenient to use one expressed *)
(* as follows in terms of an operator f:                                   *)
(*                                                                         *)
(*    AXIOM ASSUME NEW f(_), f(0), \A n \in Nat : f(n) => f(n+1)           *)
(*          PROVE  \A n \in Nat : f(n)                                     *)
(*                                                                         *)
(* However, the TLAPS proof system cannot yet handle proofs that use this  *)
(* rule.  So, for now we use this axiom.                                   *)
(***************************************************************************)
AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

(***************************************************************************)
(* We use the SimpleNatInduction rule to prove the following rule, which   *)
(* expresses the soundness of what I believe is sometimes called "General  *)
(* Induction" or "Strong Induction".                                       *)
(***************************************************************************)                                
THEOREM GeneralNatInduction == 
         \A f : /\ f[0]
                /\ \A n \in Nat : (\A j \in 0..n : f[j]) => f[n+1]
                => \A n \in Nat : f[n]
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma is used for reasoning about the operator SafeAt.    *)
(* It is proved from SafeAtProp by GeneralNatInduction.                    *)
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

-----------------------------------------------------------------------------
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
BY DEF VInv1, VInv3
-----------------------------------------------------------------------------
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

THEOREM VT1 == /\ TypeOK 
               /\ VInv1
               /\ VInv2
               => \A v, w : 
                    (v \in chosen) /\ (w \in chosen) => (v = w)
  PROOF OMITTED

THEOREM SafeAtPropPrime ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v)' =
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

-----------------------------------------------------------------------------
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
-----------------------------------------------------------------------------
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

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now come to the proof that VInv is an invariant of the               *)
(* specification.  This follows from the following result, which asserts   *)
(* that it is an inductive invariant of the next-state action.  This fact  *)
(* is used in the liveness proof as well.                                  *)
(***************************************************************************)
THEOREM InductiveInvariance == VInv /\ [Next]_vars => VInv'
  PROOF OMITTED

THEOREM InitImpliesInv == Init => VInv
  PROOF OMITTED

THEOREM VT2 == Spec => []VInv
  PROOF OMITTED

-----------------------------------------------------------------------------
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

(***************************************************************************)
(* The following theorem asserts that the safety properties of the voting  *)
(* algorithm (specified by formula Spec) of this module implement the      *)
(* consensus safety specification Spec of module Consensus under the       *)
(* substitution (refinement mapping) of the INSTANCE statement.            *)
(***************************************************************************)
THEOREM VT3 == Spec => C!Spec 
  PROOF OMITTED

-----------------------------------------------------------------------------
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
-----------------------------------------------------------------------------
(***************************************************************************)
(* We need the following simple results about sets and sets of numbers.    *)
(* The first belongs in a library of theorems about finite sets and        *)
(* cardinality.  Perhaps such a library will eventually be added to the    *)
(* FiniteSets module.                                                      *)
(***************************************************************************)
AXIOM SubsetOfFiniteSetFinite == 
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

(***************************************************************************)
(* The next result can be proved from simple facts about finite sets and   *)
(* cardinality by induction on the cardinality of S.                       *)
(***************************************************************************)
AXIOM FiniteSetHasMax == 
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

(***************************************************************************)
(* The next result can be proved from the following facts about sets       *)
(*                                                                         *)
(*   - The empty set is finite.                                            *)
(*   - A singleton set is finite.                                          *)
(*   - The union of two finite sets is finite                              *)
(*                                                                         *)
(* by induction on j-i.                                                    *)
(***************************************************************************)
AXIOM IntervalFinite == \A i, j \in Int : IsFiniteSet(i..j)
-----------------------------------------------------------------------------
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

-------------------------------------------------------------------------------
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
     \A self \in Q :
       /\ WF_vars(BallotAction(self, b))
       /\ [] [\A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
     
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
-----------------------------------------------------------------------------
(***************************************************************************)
(*                       Some Temporal Logic Proof Rules                   *)
(*                                                                         *)
(* We now state some temporal logic proof rules that are used in the       *)
(* liveness proof.  Some version of these rules will eventually be added   *)
(* to the TLAPS module.                                                    *)
(*                                                                         *)
(* The first rule is the lattice rule.  To state it, we define             *)
(* WellFounded(S, LT) to assert that the relation LT is a well-founded     *)
(* "less-than" relation on the set S.  This means that there is no         *)
(* infinite sequence of elements of S, each of which is less than the      *)
(* previous one.  We represent a relation the way mathematicians generally *)
(* do, as a set of ordered pairs.  In this case <<s, t>> \in LT means that *)
(* s is less than t.                                                       *)
(***************************************************************************)
WellFounded(S, LT) == ~ \E f \in [Nat -> S] : 
                           \A i \in Nat : <<f[i+1], f[i]>> \in LT

(***************************************************************************)
(* We now define ProperSubsetRel(S) to be the relation on a set S such     *)
(* that <<U, V>> \in S if and only if U and V are subsets of S with U a    *)
(* proper subset of V.  We then state without proof the result that, if S  *)
(* is a finite set, then ProperSubsetRel(S) is a well-founded relation on  *)
(* S.                                                                      *)
(***************************************************************************)
ProperSubsetRel(S) == 
  {r \in (SUBSET S) \X (SUBSET S) : /\ r[1] \subseteq r[2]
                                    /\ r[1] # r[2] }     
                                                     
THEOREM SubsetWellFounded ==
           \A S : IsFiniteSet(S) => WellFounded(SUBSET S, ProperSubsetRel(S))
PROOF OMITTED

(***************************************************************************)
(* Here is our statement of the Lattice Rule, which is discussed in        *)
(*                                                                         *)
(*    AUTHOR = "Leslie Lamport",                                           *)
(*    TITLE = "The Temporal Logic of Actions",                             *)
(*    JOURNAL = toplas,                                                    *)
(*    volume = 16,                                                         *)
(*    number = 3,                                                          *)
(*    YEAR = 1994,                                                         *)
(*    month = may,                                                         *)
(*    PAGES = "872--923"                                                   *)
(***************************************************************************)
THEOREM LatticeRule ==  ASSUME NEW S, NEW LT, WellFounded(S, LT),
                               NEW TEMPORAL P(_), NEW TEMPORAL Q
                        PROVE  /\ Q \/ (\E i \in S : P(i))
                               /\ \A i \in S : 
                                     P(i) ~> (Q \/ \E j \in S : (<<j, i>> \in LT) /\ P(j))
                               => ((\E i \in S : P(i)) ~> Q)
PROOF OMITTED

(***************************************************************************)
(* Here are two more temporal-logic proof rules.  Their validity is        *)
(* obvious when you understand what they mean.  We present a proof of the  *)
(* second, mostly to show how temporal logic proofs look in TLA+.  Since   *)
(* almost all the steps are temporal formulas, we don't bother trying to   *)
(* check any of them.                                                      *)
(***************************************************************************)
THEOREM AlwaysForall ==
           ASSUME NEW CONSTANT S, NEW TEMPORAL P(_)
           PROVE  (\A s \in S : []P(s)) <=> [](\A s \in S : P(s))

LEMMA EventuallyAlwaysForall == 
        ASSUME NEW CONSTANT S, IsFiniteSet(S),
               NEW TEMPORAL P(_)
        PROVE  (\A s \in S : <>[]P(s)) => <>[](\A s \in S : P(s))
(*******
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* Here is our proof that LiveSpec implements the specification LiveSpec   *)
(* of module Consensus under our refinement mapping.                       *)
(***************************************************************************)
THEOREM Liveness == LiveSpec => C!LiveSpec
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* The constant parameters and the set Ballots are the same as in the      *)
(* voting algorithm.                                                       *)
(***************************************************************************)
CONSTANT Value, Acceptor, Quorum

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor 
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
                                                                     
Ballot ==  Nat

(***************************************************************************)
(* We are going to have a leader process for each ballot and an acceptor   *)
(* process for each acceptor.  So we can use the ballot numbers and the    *)
(* acceptors themselves as the identifiers for these processes, we assume  *)
(* that the set of ballots and the set of acceptors are disjoint.  For     *)
(* good measure, we also assume that -1 is not an acceptor, although that  *)
(* is probably not necessary.                                              *)
(***************************************************************************)
ASSUME BallotAssump == (Ballot \cup {-1}) \cap Acceptor = {}

(***************************************************************************)
(* We define None to be an unspecified value that is not in the set Value. *)
(***************************************************************************)
None == CHOOSE v : v \notin Value
 
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.  A message m with m.type = "1a" is     *)
(* called a 1a message, and similarly for the other message types.         *)
(***************************************************************************)
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, 
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"1c"}, bal : Ballot, val : Value]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]
-----------------------------------------------------------------------------


(***************************************************************************)
(* The algorithm is easiest to understand in terms of the set msgs of all  *)
(* messages that have ever been sent.  A more accurate model would use one *)
(* or more variables to represent the messages actually in transit, and it *)
(* would include actions representing message loss and duplication as well *)
(* as message receipt.                                                     *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss explicitly. *)
(* The safety part of the spec says only what messages may be received and *)
(* does not assert that any message actually is received.  Thus, there is  *)
(* no difference between a lost message and one that is never received.    *)
(* The liveness property of the spec will make it clear what messages must *)
(* be received (and hence either not lost or successfully retransmitted if *)
(* lost) to guarantee progress.                                            *)
(*                                                                         *)
(* Another advantage of maintaining the set of all messages that have ever *)
(* been sent is that it allows us to define the state function `votes'     *)
(* that implements the variable of the same name in the voting algorithm   *)
(* without having to introduce a history variable.                         *)
(***************************************************************************)
(***********

In addition to the variable msgs, the algorithm uses four variables
whose values are arrays indexed by acceptor, where for any acceptor
`a':

  maxBal[a]  The largest ballot number in which `a' has participated
  
  maxVBal[a] The largest ballot number in which a has voted, or -1
             if it has never voted.   
             
  maxVVal[a] If `a' has voted, then this is the value it voted for in
             ballot maxVBal; otherwise it equals None.
             
As in the voting algorithm, an execution of the algorithm consists of an 
execution of zero or more ballots.  Different ballots may be in progress 
concurrently, and ballots may not complete (and need not even start).
A ballot b consists of the following actions (which need not all occur
in the indicated order).  

  Phase1a : The leader sends a 1a message for ballot b
  
  Phase1b : If maxBal[a] < b, an acceptor `a' responds to the 1a message by
            setting maxBal[a] to b and sending a 1b message to the leader
            containing the values of maxVBal[a] and maxVVal[a].
            
  Phase1c : When the leader has received ballot-b 1b messages from a 
            quorum, it determines some set of values that are safe
            at b and sends 1c messages for them.
            
  Phase2a : The leader sends a 2a message for some value for which it has
            already sent a ballot-b 1c message.
            
  Phase2b : Upon receipt of the 2a message, if maxBal[a] =< b, an
            acceptor `a' sets maxBal[a] and maxVBal[a] to b, sets
            maxVVal[a] to the value in the 2a message, and votes for
            that value in ballot b by sending the appropriate 2b
            message.

Here is the PlusCal code for the algorithm, which we call PCon.

--algorithm PCon {
  variables maxBal  = [a \in Acceptor |-> -1] ,
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            msgs = {}
  define {
    sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}
    
    (***********************************************************************)
    (* We define ShowsSafeAt so that ShowsSafeAt(Q, b, v) is true for a    *)
    (* quorum Q iff msgs contain ballot-b 1b messages from the acceptors   *)
    (* in Q show that v is safe at b.                                      *)
    (***********************************************************************)
    ShowsSafeAt(Q, b, v) ==
      LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
      IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
          /\ \/ \A m \in Q1b : m.mbal = -1
             \/ \E m1c \in msgs :
                  /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v] 
                  /\ \A m \in Q1b : /\ m1c.bal \geq m.mbal 
                                    /\ (m1c.bal = m.mbal) => (m.mval = v)

    }
 
  (*************************************************************************)
  (*                               The Actions                             *)
  (* As before, we describe each action as a macro.                        *)
  (*                                                                       *)
  (* The leader for process `self' can execute a Phase1a() action, which   *)
  (* sends the ballot `self' 1a message.                                   *)
  (*************************************************************************)
  macro Phase1a() { msgs := msgs \cup {[type |-> "1a", bal |-> self]} ; }
  
  (*************************************************************************)
  (* Acceptor `self' can perform a Phase1b(b) action, which is enabled iff *)
  (* b > maxBal[self].  The action sets maxBal[self] to b and sends a      *)
  (* phase 1b message to the leader containing the values of maxVBal[self] *)
  (* and maxVVal[self].                                                    *)
  (*************************************************************************)
  macro Phase1b(b) {
    when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {});
    maxBal[self] := b;
    msgs := msgs \cup {[type |-> "1b", acc |-> self, bal |-> b, 
                        mbal |-> maxVBal[self], mval |-> maxVVal[self]]} ;
   }

  (*************************************************************************)
  (* The ballot `self' leader can perform a Phase1c(S) action, which sends *)
  (* a set S of 1c messages indicating that the value in the val field of  *)
  (* each of them is safe at ballot b.  In practice, S will either contain *)
  (* a single message, or else will have a message for each possible       *)
  (* value, indicating that all values are safe.  In the first case, the   *)
  (* leader will immediately send a 2a message with the value contained in *)
  (* that single message.  (Both logical messages will be sent in the same *)
  (* physical message.) In the latter case, the leader is informing the    *)
  (* acceptors that all values are safe.  (All those logical messages      *)
  (* will, of course, be encoded in a single physical message.)            *)
  (*************************************************************************)
  macro Phase1c(S) {
    when \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v) ;
    msgs := msgs \cup {[type |-> "1c", bal |-> self, val |-> v] : v \in S} 
   }

  (*************************************************************************)
  (* The ballot `self' leader can perform a Phase2a(v) action, sending a   *)
  (* 2a message for value v, if it has not already sent a 2a message (for  *)
  (* this ballot) and it has sent a ballot `self' 1c message with val      *)
  (* field v.                                                              *)
  (*************************************************************************)
  macro Phase2a(v) {
    when /\ sentMsgs("2a", self) = {} 
         /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs ;
    msgs := msgs \cup {[type |-> "2a", bal |-> self, val |-> v]} 
   }

  (*************************************************************************)
  (* The Phase2b(b) action is executed by acceptor `self' in response to a *)
  (* ballot-b 2a message.  Note this action can be executed multiple times *)
  (* by the acceptor, but after the first one, all subsequent executions   *)
  (* are stuttering steps that do not change the value of any variable.    *)
  (*************************************************************************)
  macro Phase2b(b) {
    when b \geq maxBal[self] ;
    with (m \in sentMsgs("2a", b)) {
      maxBal[self]  := b ;
      maxVBal[self] := b ;
      maxVVal[self] := m.val;
      msgs := msgs \cup {[type |-> "2b", acc |-> self, 
                             bal |-> b, val |-> m.val]}
    }
   }
   
  (*************************************************************************)
  (* An acceptor performs the body of its `while' loop as a single atomic  *)
  (* action by nondeterministically choosing a ballot in which its Phase1b *)
  (* or Phase2b action is enabled and executing that enabled action.  If   *)
  (* no such action is enabled, the acceptor does nothing.                 *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc: while (TRUE) { 
           with (b \in Ballot) { either Phase1b(b) or Phase2b(b) 
          }
    }
   }

  (*************************************************************************)
  (* The leader of a ballot nondeterministically chooses one of its        *)
  (* actions that is enabled (and the argument for which it is enabled)    *)
  (* and performs it atomically.  It does nothing if none of its actions   *)
  (* is enabled.                                                           *)
  (*************************************************************************)
  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a() 
          or     with (S \in SUBSET Value) { Phase1c(S) }
          or     with (v \in Value) { Phase2a(v) }
         }
   }

}

The translator produces the following TLA+ specification of the algorithm.
Some blank lines have been deleted.
************)
\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVVal, msgs

(* define statement *)
sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ \E m1c \in msgs :
              /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v]
              /\ \A m \in Q1b : /\ m1c.bal \geq m.mbal
                                /\ (m1c.bal = m.mbal) => (m.mval = v)

vars == << maxBal, maxVBal, maxVVal, msgs >>

ProcSet == (Acceptor) \cup (Ballot)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ msgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ msgs' = (msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                                               mbal |-> maxVBal[self], mval |-> maxVVal[self]]})
                       /\ UNCHANGED <<maxVBal, maxVVal>>
                    \/ /\ b \geq maxBal[self]
                       /\ \E m \in sentMsgs("2a", b):
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]
                            /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                            /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
                            /\ msgs' = (msgs \cup {[type |-> "2b", acc |-> self,
                                                       bal |-> b, val |-> m.val]})

leader(self) == /\ \/ /\ msgs' = (msgs \cup {[type |-> "1a", bal |-> self]})
                   \/ /\ \E S \in SUBSET Value:
                           /\ \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v)
                           /\ msgs' = (msgs \cup {[type |-> "1c", bal |-> self, val |-> v] : v \in S})
                   \/ /\ \E v \in Value:
                           /\ /\ sentMsgs("2a", self) = {}
                              /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs
                           /\ msgs' = (msgs \cup {[type |-> "2a", bal |-> self, val |-> v]})
                /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now rewrite the next-state relation in a way that makes it easier to *)
(* use in a proof.  We start by defining the formulas representing the     *)
(* individual actions.  We then use them to define the formula TLANext,    *)
(* which is the next-state relation we would have written had we specified *)
(* the algorithm directly in TLA+ rather than in PlusCal.                  *)
(***************************************************************************)
Phase1a(self) ==
  /\ msgs' = (msgs \cup {[type |-> "1a", bal |-> self]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1c(self, S) ==
  /\ \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v)
  /\ msgs' = (msgs \cup {[type |-> "1c", bal |-> self, val |-> v] : v \in S})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase2a(self, v) ==
  /\ sentMsgs("2a", self) = {}
  /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs
  /\ msgs' = (msgs \cup {[type |-> "2a", bal |-> self, val |-> v]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1b(self, b) ==
  /\ b > maxBal[self]
  /\ sentMsgs("1a", b) # {}
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ msgs' = msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                         mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED <<maxVBal, maxVVal>>

Phase2b(self, b) ==
  /\ b \geq maxBal[self]
  /\ \E m \in sentMsgs("2a", b):
       /\ maxBal' = [maxBal EXCEPT ![self] = b]
       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
       /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
       /\ msgs' = (msgs \cup {[type |-> "2b", acc |-> self,
                               bal |-> b, val |-> m.val]})

TLANext ==
  \/ \E self \in Acceptor : 
        \E b \in Ballot : \/ Phase1b(self, b) 
                          \/ Phase2b(self,b) 
  \/ \E self \in Ballot :
        \/ Phase1a(self)
        \/ \E S \in SUBSET Value : Phase1c(self, S)
        \/ \E v \in Value : Phase2a(self, v)

(***************************************************************************)
(* The following theorem specifies the relation between the next-state     *)
(* relation Next obtained by translating the PlusCal code and the          *)
(* next-state relation TLANext.                                            *)
(***************************************************************************)
THEOREM NextDef == (Next <=> TLANext) 
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* The type invariant.                                                     *)
(***************************************************************************)
TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message    

(***************************************************************************)
(* Here is the definition of the state-function `chosen' that implements   *)
(* the state-function of the same name in the voting algorithm.            *)
(***************************************************************************)
chosen == {v \in Value : \E Q \in Quorum, b \in Ballot :
                           \A a \in Q : \E m \in msgs : /\ m.type = "2b"
                                                        /\ m.acc  = a
                                                        /\ m.bal  = b
                                                        /\ m.val  = v} 
----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the refinement mapping under which this algorithm         *)
(* implements the specification in module Voting.                          *)
(***************************************************************************)

(***************************************************************************)
(* As we observed, votes are registered by sending phase 2b messages.  So  *)
(* the array `votes' describing the votes cast by the acceptors is defined *)
(* as follows.                                                             *)
(***************************************************************************)
votes == [a \in Acceptor |->  
           {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "2b"
                                                   /\ mm.acc = a }}]
                                                   
(***************************************************************************)
(* We now instantiate module Voting, substituting:                         *)
(*                                                                         *)
(*  - The constants Value, Acceptor, and Quorum declared in this module    *)
(*    for the corresponding constants of that module Voting.               *)
(*                                                                         *)
(*  - The variable maxBal and the defined state function `votes' for the   *)
(*    correspondingly-named variables of module Voting.                    *)
(***************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define PInv to be what I believe to be an inductive invariant    *)
(* and assert the theorems for proving that this algorithm implements the  *)
(* voting algorithm under the refinement mapping specified by the INSTANCE *)
(* statement.  Whether PInv really is an inductive invariant will be       *)
(* determined only by a rigorous proof.                                    *)
(***************************************************************************)
PAccInv == \A a \in Acceptor : 
             /\ maxBal[a] >= maxVBal[a]
             /\ \A b \in (maxVBal[a]+1)..(maxBal[a]-1) : V!DidNotVoteIn(a,b)
             /\ (maxVBal[a] # -1) => V!VotedFor(a, maxVBal[a], maxVVal[a])
             
P1bInv == \A m \in msgs :
             (m.type = "1b") => 
               /\ (maxBal[m.acc] >= m.bal) /\ (m.bal > m.mbal)
               /\ \A b \in (m.mbal+1)..(m.bal-1) : V!DidNotVoteIn(m.acc,b)

P1cInv ==  \A m \in msgs : (m.type = "1c") => V!SafeAt(m.bal, m.val)

P2aInv == \A m \in msgs : 
            (m.type = "2a") => \E m1c \in msgs : /\ m1c.type = "1c"
                                                 /\ m1c.bal = m.bal 
                                                 /\ m1c.val = m.val
(***************************************************************************)
(* The following theorem is interesting in its own right.  It essentially  *)
(* asserts the correctness of the definition of ShowsSafeAt.               *)
(***************************************************************************)
THEOREM PT1 == TypeOK /\ P1bInv /\ P1cInv =>
                 \A Q \in Quorum, b \in Ballot, v \in Value :
                     ShowsSafeAt(Q, b, v) => V!SafeAt(b, v) 

PInv == TypeOK /\ PAccInv /\ P1bInv /\ P1cInv /\ P2aInv  

THEOREM Invariance == Spec => []PInv

THEOREM Implementation == Spec => V!Spec

(***************************************************************************)
(* The following result shows that our definition of `chosen' is the       *)
(* correct one, because it implements the state-function `chosen' of the   *)
(* voting algorithm.                                                       *)
(***************************************************************************)
THEOREM Spec => [](chosen = V!chosen)

(***************************************************************************)
(* The four theorems above have been checked by TLC for a model with 3     *)
(* acceptors, 2 values, and 3 ballot numbers.  Theorem PT1 was checked as  *)
(* an invariant, therefore checking only that it is true for all reachable *)
(* states.  This model is large enough that it would most likely have      *)
(* revealed any "coding" errors in the algorithm.  We believe that the     *)
(* algorithm is well-enough understood that it is unlikely to contain any  *)
(* fundamental errors.                                                     *)
(***************************************************************************)

(***************************************************************************)
(* This module specifies a Byzantine Paxos algorithm--a version of Paxos   *)
(* in which failed acceptors and leaders can be malicious.  It is an       *)
(* abstraction and generalization of the Castro-Liskov algorithm in        *)
(*                                                                         *)
(*    author = "Miguel Castro and Barbara Liskov",                         *)
(*    title = "Practical byzantine fault tolerance and proactive           *)
(*             recovery",                                                  *)
(*    journal = ACM Transactions on Computer Systems,                      *)
(*    volume = 20,                                                         *)
(*    number = 4,                                                          *)
(*    year = 2002,                                                         *)
(*    pages = "398--461"                                                   *)
(***************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(* We need the following trivial axioms and theorem about finite sets.     *)
(***************************************************************************)
AXIOM EmptySetFinite == IsFiniteSet({})

AXIOM SingletonSetFinite == \A e : IsFiniteSet({e})

AXIOM ImageOfFiniteSetFinite == 
         \A S, f : IsFiniteSet(S) => IsFiniteSet({f[x] : x \in S})

AXIOM SubsetOfFiniteSetFinite == 
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

AXIOM UnionOfFiniteSetsFinite == 
        \A S, T : IsFiniteSet(T) /\ IsFiniteSet(S)  => IsFiniteSet(S \cup T)

THEOREM OnePlusFinite == \A S, e : IsFiniteSet(S) => IsFiniteSet(S \cup {e})
  PROOF OMITTED

----------------------------------------------------------------------------
(***************************************************************************)
(* The sets Value and Ballot are the same as in the Voting and             *)
(* PaxosConsensus specs.                                                   *)
(***************************************************************************)
CONSTANT Value

Ballot == Nat

(***************************************************************************)
(* As in module PConProof, we define None to be an unspecified value that  *)
(* is not an element of Value.                                             *)
(***************************************************************************)
None == CHOOSE v : v \notin Value
-----------------------------------------------------------------------------  
(***************************************************************************)
(* We pretend that which acceptors are good and which are malicious is     *)
(* specified in advance.  Of course, the algorithm executed by the good    *)
(* acceptors makes no use of which acceptors are which.  Hence, we can     *)
(* think of the sets of good and malicious acceptors as "prophecy          *)
(* constants" that are used only for showing that the algorithm implements *)
(* the AbstratPaxosConsensus spec.                                         *)
(*                                                                         *)
(* We can assume that a maximal set of acceptors are bad, since a bad      *)
(* acceptor is allowed to do anything--including ating like a good one.    *)
(*                                                                         *)
(* The basic idea is that the good acceptors try to execute the Paxos      *)
(* consensus algorithm, while the bad acceptors may try to prevent them.   *)
(*                                                                         *)
(* We do not distinguish between faulty and non-faulty leaders.  Safety    *)
(* must be preserved even if all leaders are malicious, so we allow any    *)
(* leader to send any syntactically correct message at any time.  (In an   *)
(* implementation, syntactically incorrect messages are simply ignored by  *)
(* non-faulty acceptors and have no effect.) Assumptions about leader      *)
(* behavior are required only for liveness.                                *)
(***************************************************************************)
CONSTANTS Acceptor,       \* The set of good (non-faulty) acceptors.
          FakeAcceptor,   \* The set of possibly malicious (faulty) acceptors.
          ByzQuorum,     
            (***************************************************************)
            (* A Byzantine quorum is set of acceptors that includes a      *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* acceptors and f bad ones, a Byzantine quorum is any set of  *)
            (* 2f+1 acceptors.                                             *)
            (***************************************************************)
          WeakQuorum     
            (***************************************************************)
            (* A weak quorum is a set of acceptors that includes at least  *)
            (* one good one.  If there are f bad acceptors, then a weak    *)
            (* quorum is any set of f+1 acceptors.                         *)
            (***************************************************************)

(***************************************************************************)
(* We define ByzAcceptor to be the set of all real or fake acceptors.      *)
(***************************************************************************)
ByzAcceptor == Acceptor \cup FakeAcceptor

(***************************************************************************)
(* As in the Paxos consensus algorithm, we assume that the set of ballot   *)
(* numbers and -1 is disjoint from the set of all (real and fake)          *)
(* acceptors.                                                              *)
(***************************************************************************)
ASSUME BallotAssump == (Ballot \cup {-1}) \cap ByzAcceptor = {}

(***************************************************************************)
(* The following are the assumptions about acceptors and quorums that are  *)
(* needed to ensure safety of our algorithm.                               *)
(***************************************************************************)
ASSUME BQA == 
          /\ Acceptor \cap FakeAcceptor = {}
          /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
          /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
          /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                                   /\ Q \cap Acceptor # {}

(***************************************************************************)
(* The following assumption is not needed for safety, but it will be       *)
(* needed to ensure liveness.                                              *)
(***************************************************************************)
ASSUME BQLA == 
          /\ \E Q \in ByzQuorum : Q \subseteq Acceptor 
          /\ \E Q \in WeakQuorum : Q \subseteq Acceptor 
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the set BMessage of all possible messages.                *)
(***************************************************************************)
1aMessage == [type : {"1a"},  bal : Ballot]
  (*************************************************************************)
  (* Type 1a messages are the same as in module PConProof.                 *)
  (*************************************************************************)
  
1bMessage == 
  (*************************************************************************)
  (* A 1b message serves the same function as a 1b message in ordinary     *)
  (* Paxos, where the mbal and mval components correspond to the mbal and  *)
  (* mval components in the 1b messages of PConProof.  The m2av component  *)
  (* is set containing all records with val and bal components equal to    *)
  (* the corresponding of components of a 2av message that the acceptor    *)
  (* has sent, except containing for each val only the record              *)
  (* corresponding to the 2av message with the highest bal component.      *)
  (*************************************************************************)
  [type : {"1b"}, bal : Ballot, 
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

1cMessage == 
  (*************************************************************************)
  (* Type 1c messages are the same as in PConProof.                        *)
  (*************************************************************************)
  [type : {"1c"}, bal : Ballot, val : Value] 

2avMessage ==
  (*************************************************************************)
  (* When an acceptor receives a 1c message, it relays that message's      *)
  (* contents to the other acceptors in a 2av message.  It does this only  *)
  (* for the first 1c message it receives for that ballot; it can receive  *)
  (* a second 1c message only if the leader is malicious, in which case it *)
  (* ignores that second 1c message.                                       *)
  (*************************************************************************)
   [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]
  (*************************************************************************)
  (* 2b messages are the same as in ordinary Paxos.                        *)
  (*************************************************************************)

BMessage == 
  1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage

(***************************************************************************)
(* We will need the following simple fact about these sets of messages.    *)
(***************************************************************************)
LEMMA BMessageLemma ==
         \A m \in BMessage :
           /\ (m \in 1aMessage) <=>  (m.type = "1a")
           /\ (m \in 1bMessage) <=>  (m.type = "1b")
           /\ (m \in 1cMessage) <=>  (m.type = "1c")
           /\ (m \in 2avMessage) <=>  (m.type = "2av")
           /\ (m \in 2bMessage) <=>  (m.type = "2b")
  PROOF OMITTED

-----------------------------------------------------------------------------


(****************************************************************************
We now give the algorithm.  The basic idea is that the set Acceptor of
real acceptors emulate an execution of the PaxosConsensus algorithm
with Acceptor as its set of acceptors.  Of course, they must do that
without knowing which of the other processes in ByzAcceptor are real
acceptors and which are fake acceptors.  In addition, they don't know
whether a leader is behaving according to the PaxosConsensus algorithm
or if it is malicious.

The main idea of the algorithm is that, before performing an action of
the PaxosConsensus algorithm, a good acceptor determines that this
action is actually enabled in that algorithm.  Since an action is
enabled by the receipt of one or more messages, the acceptor has to
determine that the enabling messages are legal PaxosConsensus messages.
Because PaxosConsensus allows a 1a message to be sent at any time, the
only acceptor action whose enabling messages must be checked is the
Phase2b action.  It is enabled iff the appropriate 1c message and 2a
message are legal.  The 1c message is legal iff the leader has received
the necessary 1b messages.  The acceptor therefore maintains a set of
1b messages that it knows have been sent, and checks that those 1b
messages enable the sending of the 1c message.

A 2a message is legal in the PaxosConsensus algorithm iff (i) the
corresponding 1c message is legal and (ii) it is the only 2a message
that the leader sends.  In the BPCon algorithm, there are no 
explicit 2a messages.  They are implicitly sent by the acceptors
when they send enough 2av messages.

We leave unspecified how an acceptor discovers what 1b messages have
been sent.  In the Castro-Liskov algorithm, this is done by having
acceptors relay messages sent by other acceptors.  An acceptor knows
that a 1b message has been sent if it receives it directly or else
receives a copy from a weak Byzantine quorum of acceptors.  A
(non-malicious) leader must determine what 1b messages acceptors know
about so it chooses a value so that a quorum of acceptors will act on
its Phase1c message and cause that value to be chosen.  However, this
is necessary only for liveness, so we ignore this for now.

In other implementations of our algorithm, the leader sends along with
the 1c message a proof that the necessary 1b messages have been sent.
The easiest way to do this is to have acceptors digitally sign their 1b
messages, so a copy of the message proves that it has been sent (by the
acceptor indicated in the message's acc field).  The necessary proofs
can also be constructed using only message authenticators (like the
ones used in the Castro-Liskov algorithm); how this is done is
described elsewhere.

In the abstract algorithm presented here, which we call
BPCon, we do not specify how acceptors learn what 1b
messages have been sent.  We simply introduce a variable knowsSent such
that knowsSent[a] represents the set of 1b messages that (good)
acceptor a knows have been sent, and have an action that
nondeterministically adds sent 1b messages to this set.

--algorithm BPCon {
  (**************************************************************************
The variables:

    maxBal[a]  = Highest ballot in which acceptor a has participated.

    maxVBal[a] = Highest ballot in which acceptor a has cast a vote
                 (sent a 2b message); or -1 if it hasn't cast a vote.

    maxVVal[a] = Value acceptor a has voted for in ballot maxVBal[a],
                  or None if maxVBal[a] = -1.

    2avSent[a] = A set of records in [val : Value, bal : Ballot] 
                 describing the 2av messages that a has sent.  A
                 record is added to this set, and any element with
                 a the same val field (and lower bal field) removed 
                 when a sends a 2av message.

    knownSent[a] = The set of 1b messages that acceptor a knows have
                   been sent.

    bmsgs = The set of all messages that have been sent.  See the
            discussion of the msgs variable in module PConProof
            to understand our modeling of message passing.
  **************************************************************************)
  variables maxBal  = [a \in Acceptor |-> -1],
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            2avSent = [a \in Acceptor |-> {}],
            knowsSent = [a \in Acceptor |-> {}],
            bmsgs = {} 
  define {
    sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}
    
    KnowsSafeAt(ac, b, v) ==
      (*********************************************************************)
      (* True for an acceptor ac, ballot b, and value v iff the set of 1b  *)
      (* messages in knowsSent[ac] implies that value v is safe at ballot  *)
      (* b in the PaxosConsensus algorithm being emulated by the good      *)
      (* acceptors.  To understand the definition, see the definition of   *)
      (* ShowsSafeAt in module PConProof and recall (a) the meaning of the *)
      (* mCBal and mCVal fields of a 1b message and (b) that the set of    *)
      (* real acceptors in a ByzQuorum forms a quorum of the               *)
      (* PaxosConsensus algorithm.                                         *)
      (*********************************************************************)
      LET S == {m \in knowsSent[ac] : m.bal = b}
      IN  \/ \E BQ \in ByzQuorum : 
               \A a \in BQ : \E m \in S : /\ m.acc = a 
                                          /\ m.mbal = -1
          \/ \E c \in 0..(b-1):
               /\ \E BQ \in ByzQuorum : 
                    \A a \in BQ : \E m \in S : /\ m.acc = a
                                               /\ m.mbal =< c
                                               /\ (m.mbal = c) => (m.mval = v)
               /\ \E WQ \in WeakQuorum :
                    \A a \in WQ : 
                      \E m \in S : /\ m.acc = a
                                   /\ \E r \in m.m2av : /\ r.bal >= c
                                                        /\ r.val = v
   }

  (*************************************************************************)
  (* We now describe the processes' actions as macros.                     *)
  (*                                                                       *)
  (* As in the Paxos consensus algorithm, a ballot `self' leader (good or  *)
  (* malicious) can execute a Phase1a ation at any time.                   *)
  (*************************************************************************)
  macro Phase1a() { bmsgs := bmsgs \cup {[type |-> "1a", bal |-> self]} ; }

  (*************************************************************************)
  (* The acceptor's Phase1b ation is similar to that of the PaxosConsensus *)
  (* algorithm.                                                            *)
  (*************************************************************************)
  macro Phase1b(b) {
   when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {}) ;
   maxBal[self] := b ;
   bmsgs := bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                         m2av |-> 2avSent[self],
                         mbal |-> maxVBal[self], mval |-> maxVVal[self]]};
   }

  (*************************************************************************)
  (* A good ballot `self' leader can send a phase 1c message for value v   *)
  (* if it knows that the messages in knowsSent[a] for a Quorum of (good)  *)
  (* acceptors imply that they know that v is safe at ballot `self', and   *)
  (* that they can convince any other acceptor that the appropriate 1b     *)
  (* messages have been sent to that it will also know that v is safe at   *)
  (* ballot `self'.                                                        *)
  (*                                                                       *)
  (* A malicious ballot `self' leader can send any phase 1c messages it    *)
  (* wants (including one that a good leader could send).  We prove safety *)
  (* with a Phase1c ation that allows a leader to be malicious.  To prove  *)
  (* liveness, we will have to assume a good leader that sends only        *)
  (* correct 1c messages.                                                  *)
  (*                                                                       *)
  (* As in the PaxosConsensus algorithm, we allow a Phase1c action to send *)
  (* a set of Phase1c messages.  (This is not done in the Castro-Liskov    *)
  (* algorithm, but seems natural in light of the PaxosConsensus           *)
  (* algorithm.)                                                           *)
  (*************************************************************************)
  macro Phase1c() {
    with (S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]) {  
      bmsgs := bmsgs \cup S }
   }

  (*************************************************************************)
  (* If acceptor `self' receives a ballot b phase 1c message with value v, *)
  (* it relays v in a phase 2av message if                                 *)
  (*                                                                       *)
  (*   - it has not already sent a 2av message in this or a later          *)
  (*     ballot and                                                        *)
  (*                                                                       *)
  (*   - the messages in knowsSent[self] show it that v is safe at b in    *)
  (*     the non-Byzantine Paxos consensus algorithm being emulated.       *)
  (*************************************************************************)
  macro Phase2av(b) {
    when /\ maxBal[self] =< b  
         /\ \A r \in 2avSent[self] : r.bal < b ;
            \* We could just as well have used r.bal # b in this condition.
    with (m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
       bmsgs := bmsgs \cup 
                 {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]};
       2avSent[self] :=  {r \in 2avSent[self] : r.val # m.val} 
                           \cup {[val |-> m.val, bal |-> b]}
      } ;
    maxBal[self]  := b ;
   }

  (*************************************************************************)
  (* Acceptor `self' can send a phase 2b message with value v if it has    *)
  (* received phase 2av messages from a Byzantine quorum, which implies    *)
  (* that a quorum of good acceptors assert that this is the first 1c      *)
  (* message sent by the leader and that the leader was allowed to send    *)
  (* that message.  It sets maxBal[self], maxVBal[self], and maxVVal[self] *)
  (* as in the non-Byzantine algorithm.                                    *)
  (*************************************************************************)
  macro Phase2b(b) {
    when maxBal[self] =< b ;
    with (v \in {vv \in Value : 
                   \E Q \in ByzQuorum :
                      \A aa \in Q : 
                         \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                       /\ m.acc = aa} ) {
        bmsgs := bmsgs \cup 
                  {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]} ;
        maxVVal[self] := v ;
      } ;
    maxBal[self] := b ;
    maxVBal[self] := b
   }
  
  (*************************************************************************)
  (* At any time, an acceptor can learn that some set of 1b messages were  *)
  (* sent (but only if they atually were sent).                            *)
  (*************************************************************************)
  macro LearnsSent(b) {
    with (S \in SUBSET sentMsgs("1b", b)) {
       knowsSent[self] := knowsSent[self] \cup S
     }
   }
  (*************************************************************************)
  (* A malicious acceptor `self' can send any acceptor message indicating  *)
  (* that it is from itself.  Since a malicious acceptor could allow other *)
  (* malicious processes to forge its messages, this action could          *)
  (* represent the sending of the message by any malicious process.        *)
  (*************************************************************************)
  macro FakingAcceptor() {
    with ( m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage : 
                   mm.acc = self} ) {
         bmsgs := bmsgs \cup {m}
     }
   }
  
  (*************************************************************************)
  (* We combine these individual actions into a complete algorithm in the  *)
  (* usual way, with separate process declarations for the acceptor,       *)
  (* leader, and fake acceptor processes.                                  *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc: while (TRUE) { 
           with (b \in Ballot) {either Phase1b(b) or Phase2av(b) 
                                  or Phase2b(b) or LearnsSent(b)}
    }
   }

  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a() or Phase1c() 
         }
   }

  process (facceptor \in FakeAcceptor) {
     facc : while (TRUE) { FakingAcceptor() }
   }
}

Below is the TLA+ translation, as produced by the translator.  (Some
blank lines have been removed.)
**************************************************************************)
\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs

(* define statement *)
sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}

KnowsSafeAt(ac, b, v) ==
  LET S == {m \in knowsSent[ac] : m.bal = b}
  IN  \/ \E BQ \in ByzQuorum :
           \A a \in BQ : \E m \in S : /\ m.acc = a
                                      /\ m.mbal = -1
      \/ \E c \in 0..(b-1):
           /\ \E BQ \in ByzQuorum :
                \A a \in BQ : \E m \in S : /\ m.acc = a
                                           /\ m.mbal =< c
                                           /\ (m.mbal = c) => (m.mval = v)
           /\ \E WQ \in WeakQuorum :
                \A a \in WQ :
                  \E m \in S : /\ m.acc = a
                               /\ \E r \in m.m2av : /\ r.bal >= c
                                                    /\ r.val = v

vars == << maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs >>

ProcSet == (Acceptor) \cup (Ballot) \cup (FakeAcceptor)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ 2avSent = [a \in Acceptor |-> {}]
        /\ knowsSent = [a \in Acceptor |-> {}]
        /\ bmsgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ bmsgs' = (bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                                                 m2av |-> 2avSent[self],
                                                 mbal |-> maxVBal[self], mval |-> maxVVal[self]]})
                       /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>
                    \/ /\ /\ maxBal[self] =< b
                          /\ \A r \in 2avSent[self] : r.bal < b
                       /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
                            /\ bmsgs' = (bmsgs \cup
                                          {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]})
                            /\ 2avSent' = [2avSent EXCEPT ![self] = {r \in 2avSent[self] : r.val # m.val}
                                                                      \cup {[val |-> m.val, bal |-> b]}]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>
                    \/ /\ maxBal[self] =< b
                       /\ \E v \in {vv \in Value :
                                      \E Q \in ByzQuorum :
                                         \A aa \in Q :
                                            \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                                          /\ m.acc = aa}:
                            /\ bmsgs' = (bmsgs \cup
                                          {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
                            /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                       /\ UNCHANGED <<2avSent, knowsSent>>
                    \/ /\ \E S \in SUBSET sentMsgs("1b", b):
                            knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
                       /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

leader(self) == /\ \/ /\ bmsgs' = (bmsgs \cup {[type |-> "1a", bal |-> self]})
                   \/ /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                           bmsgs' = (bmsgs \cup S)
                /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

facceptor(self) == /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
                                 mm.acc = self}:
                        bmsgs' = (bmsgs \cup {m})
                   /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, 
                                   knowsSent >>

Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))
           \/ (\E self \in FakeAcceptor: facceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* As in module PConProof, we now rewrite the next-state relation in a     *)
(* form more convenient for writing proofs.                                *)
(***************************************************************************)
Phase1b(self, b) == 
  /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ bmsgs' = bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                           m2av |-> 2avSent[self],
                           mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>

Phase2av(self, b) == 
  /\ maxBal[self] =< b
  /\ \A r \in 2avSent[self] : r.bal < b
  /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
       /\ bmsgs' = bmsgs \cup
                    {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]}
       /\ 2avSent' = [2avSent EXCEPT 
                        ![self] = {r \in 2avSent[self] : r.val # m.val} 
                                    \cup {[val |-> m.val, bal |-> b]}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>

Phase2b(self, b) ==
  /\ maxBal[self] =< b
  /\ \E v \in {vv \in Value :
                 \E Q \in ByzQuorum :
                    \A a \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                     /\ m.acc = a }:
       /\ bmsgs' = (bmsgs \cup
                     {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
       /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
  /\ UNCHANGED <<2avSent, knowsSent>>

LearnsSent(self, b) == 
 /\ \E S \in SUBSET sentMsgs("1b", b):
       knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
 /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>> 

Phase1a(self) == 
  /\ bmsgs' = (bmsgs \cup {[type |-> "1a", bal |-> self]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

Phase1c(self) ==
  /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                        bmsgs' = (bmsgs \cup S)
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

FakingAcceptor(self) ==
  /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage : mm.acc = self} :
         bmsgs' = (bmsgs \cup {m})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma describes how the next-state relation Next can be   *)
(* written in terms of the actions defined above.                          *)
(***************************************************************************)
LEMMA NextDef == 
 Next = \/ \E self \in Acceptor :
             \E b \in Ballot : \/ Phase1b(self, b) 
                               \/ Phase2av(self, b) 
                               \/ Phase2b(self,b)
                               \/ LearnsSent(self, b) 
        \/ \E self \in Ballot : \/ Phase1a(self)
                                \/ Phase1c(self)
        \/ \E self \in FakeAcceptor : FakingAcceptor(self)
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(*                        THE REFINEMENT MAPPING                           *)
(***************************************************************************)

(***************************************************************************)
(* We define a quorum to be the set of acceptors in a Byzantine quorum.    *)
(* The quorum assumption QA of module PConProof, which we here call        *)
(* QuorumTheorem, follows easily from the definition and assumption BQA.   *)
(***************************************************************************)
Quorum == {S \cap Acceptor : S \in ByzQuorum}

THEOREM QuorumTheorem == 
         /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
         /\ \A Q \in Quorum : Q \subseteq Acceptor
  PROOF OMITTED

THEOREM MaxBallotProp  ==
         \A S \in SUBSET (Ballot \cup {-1}) : 
            IsFiniteSet(S) => 
              IF S = {} THEN MaxBallot(S) = -1
                        ELSE /\ MaxBallot(S) \in S
                             /\ \A x \in S : MaxBallot(S) >= x
  PROOF OMITTED

LEMMA MaxBallotLemma1 ==
          \A S \in SUBSET (Ballot \cup {-1}) : 
            IsFiniteSet(S) => 
              \A y \in S :
               (\A x \in S : y >= x) => (y = MaxBallot(S))
  PROOF OMITTED

LEMMA MaxBallotLemma2 ==
         \A S, T \in SUBSET (Ballot \cup {-1}) :
            IsFiniteSet(S) /\ IsFiniteSet(T) =>
              MaxBallot(S \cup T) = IF MaxBallot(S) >= MaxBallot(T)
                                      THEN MaxBallot(S)
                                      ELSE MaxBallot(T)
  PROOF OMITTED

PmaxBal == [a \in Acceptor |-> 
              MaxBallot({m.bal : m \in {ma \in 1bOr2bMsgs : 
                                           ma.acc = a}})]

LEMMA PmaxBalLemma1 == 
         \A m : /\ bmsgs' = bmsgs \cup {m} 
                /\ m.type # "1b" /\ m.type # "2b"
                => PmaxBal' = PmaxBal
  PROOF OMITTED

LEMMA PmaxBalLemma2 ==
        \A m : (bmsgs' = bmsgs \cup {m}) =>
            \A a \in Acceptor : (m.acc # a => PmaxBal'[a] = PmaxBal[a])
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the inductive invariant Inv used in our proof.  It is     *)
(* defined to be the conjunction of a number of separate invariants that   *)
(* we define first, starting with the ever-present type-correctness        *)
(* invariant.                                                              *)
(***************************************************************************)
TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ 2avSent \in [Acceptor -> SUBSET [val : Value, bal : Ballot]]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ knowsSent \in [Acceptor -> SUBSET 1bMessage]
          /\ bmsgs \subseteq BMessage

(***************************************************************************)
(* To use the definition of PmaxBal, we need to know that the set of 1b    *)
(* and 2b messages in bmsgs is finite.  This is asserted by the following  *)
(* invariant.  Note that the set bmsgs is not necessarily finite because   *)
(* we allow a Phase1c action to send an infinite number of 1c messages.    *)
(***************************************************************************)
bmsgsFinite == IsFiniteSet(1bOr2bMsgs)

(***************************************************************************)
(* The following lemma is used to prove the invariance of bmsgsFinite.     *)
(***************************************************************************)
LEMMA FiniteMsgsLemma == 
        \A m : bmsgsFinite /\ (bmsgs' = bmsgs \cup {m}) => bmsgsFinite'
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now prove some simple lemmas that are useful for reasoning about     *)
(* PmaxBal.                                                                *)
(***************************************************************************)
LEMMA PMaxBalLemma3 == 
        ASSUME TypeOK, 
               bmsgsFinite,
               NEW a \in Acceptor
        PROVE  LET S == {m.bal : m \in {ma \in bmsgs : 
                                           /\ ma.type \in {"1b", "2b"}
                                           /\ ma.acc = a}}
               IN  /\ IsFiniteSet(S) 
                   /\ S \in SUBSET Ballot 
  PROOF OMITTED

LEMMA PmaxBalLemma4 ==
         TypeOK /\ maxBalInv /\ bmsgsFinite => 
             \A a \in Acceptor : PmaxBal[a] =< maxBal[a]
PROOF OBVIOUS

========================================