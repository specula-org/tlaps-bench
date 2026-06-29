---------------------------- MODULE BinarySearch_SortedLess ----------------------------
(***************************************************************************)
(* This module defines a binary search algorithm for finding an item in a  *)
(* sorted sequence, and contains a TLAPS-checked proof of its safety       *)
(* property.  We assume a sorted sequence seq with elements in some set    *)
(* Values of integers and a number val in Values, it sets the value        *)
(* `result' to either a number i with seq[i] = val, or to 0 if there is no *)
(* such i.                                                                 *)
(*                                                                         *)
(* It is surprisingly difficult to get such a binary search algorithm      *)
(* correct without making errors that have to be caught by debugging.  I   *)
(* suggest trying to write a correct PlusCal binary search algorithm       *)
(* yourself before looking at this one.                                    *)
(*                                                                         *)
(* This algorithm is one of the examples in Section 7.3 of "Proving Safety *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLAPS

CONSTANT Values

ASSUME ValAssump == Values \subseteq Int

SortedSeqs == {ss \in Seq(Values) : 
                 \A i, j \in 1..Len(ss) : (i < j) => (ss[i] =< ss[j])}

LEMMA SortedLess ==
    ASSUME NEW s \in SortedSeqs, NEW i \in 1 .. Len(s), NEW j \in 1 .. Len(s),
           s[i] < s[j]
    PROVE  i < j
PROOF OBVIOUS

(***************************************************************************
--fair algorithm BinarySearch {
   variables seq \in SortedSeqs, val \in Values, 
             low = 1, high = Len(seq), result = 0 ;   
   { a: while (low =< high /\ result = 0) {
          with (mid = (low + high) \div 2, mval = seq[mid]) {
            if (mval = val) { result := mid}
            else if (val < mval) { high := mid - 1}
            else {low := mid + 1}                    } } } }
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

Init == (* Global variables *)
        /\ seq \in SortedSeqs
        /\ val \in Values
        /\ low = 1
        /\ high = Len(seq)
        /\ result = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF low =< high /\ result = 0
           THEN /\ LET mid == (low + high) \div 2 IN
                     LET mval == seq[mid] IN
                       IF mval = val
                          THEN /\ result' = mid
                               /\ UNCHANGED << low, high >>
                          ELSE /\ IF val < mval
                                     THEN /\ high' = mid - 1
                                          /\ low' = low
                                     ELSE /\ low' = mid + 1
                                          /\ high' = high
                               /\ UNCHANGED result
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
(***************************************************************************)
(* Partial correctness of the algorithm is expressed by invariance of      *)
(* formula resultCorrect.  To get TLC to check this property, we use a     *)
(* model that overrides the definition of Seq so Seq(S) is the set of      *)
(* sequences of elements of S having at most some small length.  For       *)
(* example,                                                                *)
(*                                                                         *)
(*    Seq(S) == UNION {[1..i -> S] : i \in 0..3}                           *)
(*                                                                         *)
(* is the set of such sequences with length at most 3.                     *)
(***************************************************************************)
resultCorrect == 
   (pc = "Done") => IF \E i \in 1..Len(seq) : seq[i] = val
                     THEN seq[result] = val
                     ELSE result = 0 

(***************************************************************************)
(* Proving the invariance of resultCorrect requires finding an inductive   *)
(* invariant that implies it.  A suitable inductive invariant Inv is       *)
(* defined here.  You can use TLC to check that Inv is an inductive        *)
(* invariant.                                                              *)
(***************************************************************************)
TypeOK == /\ seq \in SortedSeqs
          /\ val \in Values
          /\ low \in 1..(Len(seq)+1)
          /\ high  \in 0..Len(seq)
          /\ result \in 0..Len(seq)
          /\ pc \in {"a", "Done"} 
                                   
Inv == /\ TypeOK
       /\ (result /= 0) => (Len(seq) > 0) /\ (seq[result] = val)
       /\ (pc = "a") =>
             IF \E i \in 1..Len(seq) : seq[i] = val 
               THEN \E i \in low..high : seq[i] = val
               ELSE result = 0
       /\ (pc = "Done") => (result /= 0) \/ (\A i \in 1..Len(seq) : seq[i] /= val)

(***************************************************************************)
(* Here is the invariance proof.                                           *)
(***************************************************************************)
=============================================================================
