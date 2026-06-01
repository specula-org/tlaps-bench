----------------------------- MODULE VoteProof_SafeLemma ------------------------------ 
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
EXTENDS Integers , FiniteSets, TLC, TLAPS

\* THEOREM SMT == TRUE (*{ by (smt) }*)
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
PROOF
<1>1. ASSUME TypeOK
      PROVE  \A b \in Ballot :
               \A v \in Value :
                  SafeAt(b, v) =>
                    \A c \in 0..(b-1) :
                      \E Q \in Quorum :
                        \A a \in Q : /\ maxBal[a] >= c
                                     /\ \/ DidNotVoteIn(a, c)
                                        \/ VotedFor(a, c, v)
  <2> DEFINE P(b) ==
         \A v \in Value :
            SafeAt(b, v) =>
              \A c \in 0..(b-1) :
                \E Q \in Quorum :
                  \A a \in Q : /\ maxBal[a] >= c
                               /\ \/ DidNotVoteIn(a, c)
                                  \/ VotedFor(a, c, v)
  <2>1. P(0)
    BY SMT DEF P
  <2>2. ASSUME NEW n \in Nat,
               \A j \in 0..n : P(j)
        PROVE  P(n+1)
    <3>1. ASSUME NEW v \in Value,
                 SafeAt(n+1, v),
                 NEW c \in 0..((n+1)-1)
          PROVE  \E Q \in Quorum :
                   \A a \in Q : /\ maxBal[a] >= c
                                /\ \/ DidNotVoteIn(a, c)
                                   \/ VotedFor(a, c, v)
      <4>1. n+1 \in Ballot
        BY SMT DEF Ballot
      <4>2. n+1 # 0
        BY SMT
      <4>3. SafeAt(n+1, v) =
              \/ n+1 = 0
              \/ \E Q \in Quorum :
                   /\ \A a \in Q : maxBal[a] \geq n+1
                   /\ \E e \in -1..((n+1)-1) :
                        /\ (e # -1) => /\ SafeAt(e, v)
                                           /\ \A a \in Q :
                                                \A w \in Value :
                                                  VotedFor(a, e, w) => (w = v)
                        /\ \A d \in (e+1)..((n+1)-1), a \in Q :
                             DidNotVoteIn(a, d)
        BY <3>1, <4>1, SafeAtProp
      <4>4. \E Q \in Quorum :
              /\ \A a \in Q : maxBal[a] \geq n+1
              /\ \E e \in -1..((n+1)-1) :
                   /\ (e # -1) => /\ SafeAt(e, v)
                                      /\ \A a \in Q :
                                           \A w \in Value :
                                             VotedFor(a, e, w) => (w = v)
                   /\ \A d \in (e+1)..((n+1)-1), a \in Q :
                        DidNotVoteIn(a, d)
        BY <3>1, <4>2, <4>3, Zenon
      <4>5. PICK Q \in Quorum,
                   e \in -1..((n+1)-1) :
               /\ \A a \in Q : maxBal[a] \geq n+1
               /\ /\ (e # -1) => /\ SafeAt(e, v)
                                  /\ \A a \in Q :
                                       \A w \in Value :
                                         VotedFor(a, e, w) => (w = v)
                  /\ \A d \in (e+1)..((n+1)-1), a \in Q :
                       DidNotVoteIn(a, d)
        BY <4>4
      <4>6. CASE c < e
        <5>1. e \in 0..n
          BY <3>1, <4>5, <4>6, SMT DEF Ballot
        <5>2. P(e)
          BY <2>2, <5>1, SMT
        <5>3. QED
          BY <3>1, <4>5, <4>6, <5>1, <5>2, SMT DEF P
      <4>7. CASE c = e
        <5>1. ASSUME NEW a \in Q
              PROVE  /\ maxBal[a] >= c
                     /\ \/ DidNotVoteIn(a, c)
                        \/ VotedFor(a, c, v)
          <6>1. c <= n+1
            BY <3>1, SMT
          <6>2. maxBal[a] >= n+1
            BY <4>5, <5>1
          <6>3. a \in Acceptor
            BY QA, <4>5, <5>1, SMT
          <6>4. maxBal[a] \in Ballot \cup {-1}
            BY TypeOK, <6>3 DEF TypeOK
          <6>5. maxBal[a] \geq c
            BY <4>7, <6>1, <6>2, <6>4, SMT DEF Ballot
          <6>6. CASE DidNotVoteIn(a, c)
            BY <6>5, <6>6
          <6>7. CASE ~ DidNotVoteIn(a, c)
            <7>1. PICK w \in Value : VotedFor(a, c, w)
              BY <6>7 DEF DidNotVoteIn
            <7>2. w = v
              BY <4>5, <4>7, <5>1, <7>1, SMT
            <7>3. QED
              BY <6>5, <7>1, <7>2, SMT
          <6>8. QED
            BY <6>6, <6>7, SMT
        <5>2. QED
          BY <4>5, <5>1, SMT
      <4>8. CASE c > e
        <5>1. ASSUME NEW a \in Q
              PROVE  /\ maxBal[a] >= c
                     /\ \/ DidNotVoteIn(a, c)
                        \/ VotedFor(a, c, v)
          <6>1. c <= n+1
            BY <3>1, SMT
          <6>2. maxBal[a] >= n+1
            BY <4>5, <5>1
          <6>3. a \in Acceptor
            BY QA, <4>5, <5>1, SMT
          <6>4. maxBal[a] \in Ballot \cup {-1}
            BY TypeOK, <6>3 DEF TypeOK
          <6>5. maxBal[a] \geq c
            BY <6>1, <6>2, <6>4, SMT DEF Ballot
          <6>6. DidNotVoteIn(a, c)
            BY <3>1, <4>5, <4>8, <5>1, SMT
          <6>7. QED
            BY <6>5, <6>6
        <5>2. QED
          BY <4>5, <5>1, SMT
      <4>9. QED
        BY <4>6, <4>7, <4>8, SMT
    <3>2. QED
      BY <3>1, SMT DEF P
  <2>3. \A b \in Nat : P(b)
    <3> DEFINE F == [i \in Nat |-> P(i)]
    <3>1. F[0]
      BY <2>1 DEF F
    <3>2. \A n \in Nat : (\A j \in 0..n : F[j]) => F[n+1]
      BY <2>2 DEF F
    <3>3. \A n \in Nat : F[n]
      BY <3>1, <3>2, GeneralNatInduction
    <3>4. QED
      BY <3>3 DEF F
  <2>4. QED
    BY <2>3 DEF P, Ballot
<1>2. QED
  BY <1>1

===============================================================================
