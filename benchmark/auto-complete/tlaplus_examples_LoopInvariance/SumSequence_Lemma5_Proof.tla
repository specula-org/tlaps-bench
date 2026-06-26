---------------------------- MODULE SumSequence_Lemma5_Proof ----------------------------
(***************************************************************************)
(* This module contains a trivial PlusCal algorithm to sum the elements of *)
(* a sequence of integers, together with its non-trivial complete          *)
(* TLAPS-checked proof.                                                    *)
(*                                                                         *)
(* This algorithm is one of the examples in Section 7.3 of "Proving Safety *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, SequenceTheorems, SequencesExtTheorems, NaturalsInduction, TLAPS

(***************************************************************************)
(* To facilitate model checking, we assume that the sequence to be summed  *)
(* consists of integers in a set Values of integers.                       *)
(***************************************************************************)
CONSTANT Values
ASSUME  ValAssump == Values \subseteq Int

(***************************************************************************)
(* In order to be able to express correctness of the algorithm, we define  *)
(* in TLA+ an operator SeqSum so that, if s is the sequence                *)
(*                                                                         *)
(*    s_1, ... , s_n                                                       *)
(*                                                                         *)
(* of integers, then SumSeq(s) equals                                      *)
(*                                                                         *)
(*    s_1 + ... + s_n                                                      *)
(*                                                                         *)
(* The obvious TLA+ definition of SeqSum is                                *)
(*                                                                         *)
(*    RECURSIVE SeqSum(_)                                                  *)
(*    SeqSum(s) == IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))         *)
(*                                                                         *)
(* However, TLAPS does not yet handle recursive operator definitions, but  *)
(* it does handle recursive function definitions.  So, we define SeqSum in *)
(* terms of a recursively defined function.                                *)
(***************************************************************************)
SeqSum(s) == 
  LET SS[ss \in Seq(Int)] == IF ss = << >> THEN 0 ELSE ss[1] + SS[Tail(ss)]
  IN  SS[s]

(***************************************************************************
Here's the algorithm.  It initially sets seq to an arbitrary sequence
of integers in Values and leaves its value unchanged.  It terminates
with the variable sum equal to the sum of the elements of seq.

--fair algorithm SumSequence {
    variables seq \in Seq(Values), sum = 0, n = 1 ;
    { a: while (n =< Len(seq)) 
          { sum := sum + seq[n] ;
             n := n+1 ;           }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES pc, seq, sum, n

vars == << pc, seq, sum, n >>

Init == (* Global variables *)
        /\ seq \in Seq(Values)
        /\ sum = 0
        /\ n = 1
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF n =< Len(seq)
           THEN /\ sum' = sum + seq[n]
                /\ n' = n+1
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << sum, n >>
     /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
(***************************************************************************)
(* Correctness of the algorithm means that it satisfies these two          *)
(* properties:                                                             *)
(*                                                                         *)
(*   - Safety: If it terminates, then it does so with sum equal to         *)
(*             SeqSum(seq).                                                *)
(*                                                                         *)
(*   - Liveness: The algorithm eventually terminates.                      *)
(*                                                                         *)
(* Safety is expressed in TLA+ by the invariance of the following          *)
(* postcondition.                                                          *)
(***************************************************************************)
PCorrect == (pc = "Done") => (sum = SeqSum(seq))

(***************************************************************************)
(* To get TLC to check that the algorithm is correct, we use a model that  *)
(* overrides the definition of Seq so Seq(S) is the set of sequences of    *)
(* elements of S having at most some small length.  For example,           *)
(*                                                                         *)
(*    Seq(S) == UNION {[1..i -> S] : i \in 0..3}                           *)
(*                                                                         *)
(* is the set of such sequences with length at most 3.                     *)
(***************************************************************************)
(***************************************************************************)
(*                           The Proof of Safety                           *)
(*                                                                         *)
(* To prove the invariance of the postcondition, we need to find an        *)
(* inductive invariant that implies it.  A suitable inductive invariant is *)
(* formula Inv defined here.                                               *)
(***************************************************************************)
TypeOK == /\ seq \in Seq(Values)
          /\ sum \in Int
          /\ n \in 1..(Len(seq)+1)
          /\ pc \in {"a", "Done"}
          
Inv == /\ TypeOK
       /\ sum = SeqSum([i \in 1..(n-1) |-> seq[i]])
       /\ (pc = "Done") => (n = Len(seq) + 1) 
       
(***************************************************************************)
(* TLC can check that Inv is an inductive invariant on a large enough      *)
(* model to give us confidence in its correctness.  We can therefore try   *)
(* to use it to prove the postcondition.                                   *)
(***************************************************************************)
(***************************************************************************)
(* In the course of writing the proof, I found that I needed two simple    *)
(* simple properties of sequences and SeqSum.  The first essentially       *)
(* states that the definition of SeqSum is correct--that is, that it       *)
(* defines the operator we expect it to.  TLA+ doesn't require you to      *)
(* prove anything when making a definition, and it allows you to write     *)
(* silly recursive definitions like                                        *)
(*                                                                         *)
(*    RECURSIVE NotFactorial(_)                                            *)
(*    NotFactorial(i) == IF i = 0 THEN 1 ELSE i * NotFactorial(i+1)        *)
(*                                                                         *)
(* Writing this definition doesn't mean that NonFactorial(4) actually      *)
(* equals 4 * NonFactorial(5).  I think it actually does, but I'm not      *)
(* sure.  I do know that it doesn't imply that NonFactorial(4) is a        *)
(* natural number.  But the recursive definition of SeqSum is sensible,    *)
(* and we can prove the following lemma, which implies that                *)
(* SeqSum(<<1, 2, 3, 4>>) equals 1 + SeqSum(<<2, 3, 4>>).                  *)
(***************************************************************************)
LEMMA Lemma1 ==
        \A s \in Seq(Int) : 
          SeqSum(s) = IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))

(***************************************************************************)
(* What makes a formal proof of the algorithm non-trivial is that the      *)
(* definition of SeqSum essentially computes SeqSum(seq) by summing the    *)
(* elements of seq from left to right, starting with seq[1].  However, the *)
(* algorithm sums the elements from right to left, starting with           *)
(* seq[Len(s)].  Proving the correctness of the algorithm requires proving *)
(* that the two ways of computing the sum produce the same result.  To     *)
(* state that result, it's convenient to define the operator Front on      *)
(* sequences to be the mirror image of Tail:                               *)
(*                                                                         *)
(*   Front(<<1, 2, 3, 4>>)  =  <<2, 3, 4>>                                 *)
(*                                                                         *)
(* This operator is defined in the SequenceTheorems module.  I find it     *)
(* more convenient to use the slightly different definition expressed by   *)
(* this theorem.                                                           *)
(***************************************************************************)
THEOREM FrontDef  ==  \A S : \A s \in Seq(S) :
                        Front(s) = [i \in 1..(Len(s)-1) |-> s[i]]
PROOF OMITTED

LEMMA Lemma5  ==  \A s \in Seq(Int) : 
                    (Len(s) > 0) => 
                       (SeqSum(s) =  SeqSum(Front(s)) + s[Len(s)])

(***************************************************************************)
(* If we're interested in correctness of an algorithm, we probably don't   *)
(* want to spend our time proving simple properties of data types.         *)
(* Instead of proving these two obviously correct lemmas, it's best to     *)
(* check them with TLC to make sure we haven't made some silly mistake in  *)
(* writing them, and to prove correctness of the algorithm.  If we want to *)
(* be sure that the lemmas are correct, we can then prove them.  Proofs of *)
(* these lemmas are given below.                                           *)
(***************************************************************************)
THEOREM Spec => []PCorrect
PROOF OMITTED
(***************************************************************************)
(*                          Proofs of the Lemmas.                          *)
(***************************************************************************)

(***************************************************************************)
(* The LET definition at the heart of the definition of SeqSum is a        *)
(* standard definition of a function on sequences by tail recursion.       *)
(* Theorem TailInductiveDef of module SequenceTheorems proves correctness  *)
(* of such a definition.                                                   *)
(***************************************************************************)
LEMMA Lemma1_Proof ==
         \A s \in Seq(Int) : 
          SeqSum(s) = IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))
PROOF OMITTED

(***************************************************************************)
(* Lemmas 2 and 3 are simple properties of Tail and Front that are used in *)
(* the proof of Lemma 5.                                                   *)
(***************************************************************************)
LEMMA Lemma2 == 
       \A S : \A s \in Seq(S) :
          Len(s) > 0 => /\ Tail(s) \in Seq(S)
                        /\ Front(s) \in Seq(S)
                        /\ Len(Tail(s)) = Len(s) - 1
                        /\ Len(Front(s)) = Len(s) - 1
PROOF OMITTED

LEMMA Lemma2a ==
  ASSUME NEW S, NEW s \in Seq(S), Len(s) > 1
  PROVE  Tail(s) = [i \in 1..(Len(s) - 1) |-> s[i+1]]
PROOF OMITTED

LEMMA Lemma3 ==
  \A S : \A s \in Seq(S) :
            (Len(s) > 1) => (Tail(Front(s)) = Front(Tail(s)))
PROOF OMITTED

(***************************************************************************)
(* The following lemma asserts type correctness of the SeqSum operator.    *)
(* It's proved by induction on the length of its argument.  Such simple    *)
(* induction is expressed by theorem NatInduction of module                *)
(* NaturalsInduction.                                                      *)
(***************************************************************************)
LEMMA Lemma4 == \A s \in Seq(Int) : SeqSum(s) \in Int
PROOF OMITTED

LEMMA Lemma5_Proof ==
        \A s \in Seq(Int) : 
          (Len(s) > 0) => 
            SeqSum(s) =  SeqSum(Front(s)) + s[Len(s)]
PROOF OBVIOUS
=============================================================================
\* Modification History
\* Created Fri Apr 19 14:13:06 PDT 2019 by lamport
