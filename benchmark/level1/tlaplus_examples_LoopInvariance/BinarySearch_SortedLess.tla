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

=============================================================================