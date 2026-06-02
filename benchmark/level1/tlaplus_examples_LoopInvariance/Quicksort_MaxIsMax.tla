----------------------------- MODULE Quicksort_MaxIsMax -----------------------------
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* If you are not already familiar with that algorithm, you should look it *)
(* up on the Web and understand how it works--including what the partition *)
(* procedure does, without worrying about how it does it.  The version     *)
(* presented here does not specify a partition procedure, but chooses in a *)
(* single step an arbitrary value that is the result that any partition    *)
(* procedure may produce.                                                  *)
(*                                                                         *)
(* The module also has a structured informal proof of Quicksort's partial  *)
(* correctness property--namely, that if it terminates, it produces a      *)
(* sorted permutation of the original sequence.  As described in the note  *)
(* "Proving Safety Properties", the proof uses the TLAPS proof system to   *)
(* check the decomposition of the proof into substeps, and to check some   *)
(* of the substeps whose proofs are trivial.                               *)
(*                                                                         *)
(* The version of Quicksort described here sorts a finite sequence of      *)
(* integers.  It is one of the examples in Section 7.3 of "Proving Safety  *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems, FiniteSetTheorems
  (*************************************************************************)
  (* This statement imports some standard modules, including ones used by  *)
  (* the TLAPS proof system.                                               *)
  (*************************************************************************)

(***************************************************************************)
(* To aid in model checking the spec, we assume that the sequence to be    *)
(* sorted are elements of a set Values of integers.                        *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* We define PermsOf(s) to be the set of permutations of a sequence s of   *)
(* integers.  In TLA+, a sequence is a function whose domain is the set    *)
(* 1..Len(s).  A permutation of s is the composition of s with a           *)
(* permutation of its domain.  It is defined as follows, where:            *)
(*                                                                         *)
(*  - Automorphisms(S) is the set of all permutations of S, if S is a      *)
(*    finite set--that is all functions f from S to S such that every      *)
(*    element y of S is the image of some element of S under f.            *)
(*                                                                         *)
(*  - f ** g  is defined to be the composition of the functions f and g.   *)
(*                                                                         *)
(* In TLA+, DOMAIN f is the domain of a function f.                        *)
(***************************************************************************)
Automorphisms(S) == { f \in [S -> S] : 
                        \A y \in S : \E x \in S : f[x] = y }

f ** g == [x \in DOMAIN g |-> f[g[x]]]

PermsOf(s) == { s ** f : f \in Automorphisms(DOMAIN s) }

LEMMA AutomorphismsCompose ==
    ASSUME NEW S, NEW f \in Automorphisms(S), NEW g \in Automorphisms(S)
    PROVE  f ** g \in Automorphisms(S)
  PROOF OMITTED

LEMMA PermsOfLemma ==
    ASSUME NEW T, NEW s \in Seq(T), NEW t \in PermsOf(s)
    PROVE  /\ t \in Seq(T)
           /\ Len(t) = Len(s)
           /\ \A i \in 1 .. Len(s) : \E j \in 1 .. Len(s) : t[i] = s[j]
           /\ \A i \in 1 .. Len(s) : \E j \in 1 .. Len(t) : t[j] = s[i]
  PROOF OMITTED

LEMMA PermsOfPermsOf ==
    ASSUME NEW T, NEW s \in Seq(T), NEW t \in PermsOf(s), NEW u \in PermsOf(t)
    PROVE  u \in PermsOf(s)
  PROOF OMITTED

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

LEMMA MinIsMin == 
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x <= y
    PROVE  x = Min(S)
  PROOF OMITTED

LEMMA MaxIsMax == 
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x >= y
    PROVE  x = Max(S)
PROOF OBVIOUS

=============================================================================