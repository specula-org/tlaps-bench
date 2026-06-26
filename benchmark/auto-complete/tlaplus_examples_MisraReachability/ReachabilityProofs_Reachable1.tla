------------------------- MODULE ReachabilityProofs_Reachable1 -------------------------
(***************************************************************************)
(* This module contains several lemmas about the operator ReachableFrom    *)
(* defined in module Reachability.  Their proofs have been checked with    *)
(* the TLAPS proof system.  The proofs contain comments explaining how     *)
(* such proofs are written.                                                *)
(*                                                                         *)
(* Lemmas Reachable1, Reachable2, and Reachable3 are used to prove         *)
(* correctness of the algorithm in module Reachable.  Lemma Reachable0 is  *)
(* used in the proof of lemmas Reachable1 and Reachable3.  You might want  *)
(* to read the proofs in module Reachable before reading any further.      *)
(*                                                                         *)
(* All the lemmas except Reachable1 are obvious consequences of the        *)
(* definition of ReachableFrom.                                            *)
(***************************************************************************)
EXTENDS Reachability, NaturalsInduction, TLAPS

(***************************************************************************)
(* This lemma is quite trivial.  It's a good warmup exercise in using      *)
(* TLAPS to reason about data structures.                                  *)
(***************************************************************************)
LEMMA Reachable0 ==
       \A S \in SUBSET Nodes : 
           \A n \in S : n \in ReachableFrom(S)
  (*************************************************************************)
  (* Applying the Decompose Proof command to the lemma generates the       *)
  (* following statement.                                                  *)
  (*************************************************************************)
PROOF OMITTED

(***************************************************************************)
(* The following lemma lies at the heart of the correctness of the         *)
(* algorithm in module Reachable.  The lemma is not obviously true.  To    *)
(* write a proof that TLAPS can check, we need to start with an informal   *)
(* proof and then formalize that proof in TLA+.  A mathematician should be *)
(* able to devise an informal proof of this lemma in her head.  Others     *)
(* will have to write it down.  The informal proof that I came up with     *)
(* appears as comments placed at the appropriate points in the TLA+ proof. *)
(* I devised the informal proof before I started writing the TLA+ proof.   *)
(* But it's easier to read that informal proof by using the higher levels  *)
(* of the TLA+ proof to give it the proper hierarchical structure.  The    *)
(* best way to read the proof hierarchically is in the Toolbox, clicking   *)
(* on the little + and - icons beside a step to show and hide the step's   *)
(* proof.  Start by executing the Hide Current Subtree command on the      *)
(* lemma.                                                                  *)
(***************************************************************************)
LEMMA Reachable1 == 
        \A S, T \in SUBSET Nodes : 
          (\A n \in S : Succ[n] \subseteq (S \cup T))
            => (S \cup ReachableFrom(T)) = ReachableFrom(S \cup T)
  (*************************************************************************)
  (* An informal proof usually begins by implicitly assuming the following *)
  (* step.                                                                 *)
  (*************************************************************************)
PROOF OBVIOUS

(***************************************************************************)
(* The proof of this lemma is straightforward.                             *)
(***************************************************************************)

(***************************************************************************)
(* This lemma is quite obvious.                                            *)
(***************************************************************************)                 
=============================================================================
\* Modification History
\* Last modified Sat Apr 13 18:07:57 PDT 2019 by lamport
\* Created Thu Apr 11 18:19:10 PDT 2019 by lamport
