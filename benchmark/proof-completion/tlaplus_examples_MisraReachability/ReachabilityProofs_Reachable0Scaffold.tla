------------------------- MODULE ReachabilityProofs_Reachable0Scaffold -------------------------
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
=============================================================================
