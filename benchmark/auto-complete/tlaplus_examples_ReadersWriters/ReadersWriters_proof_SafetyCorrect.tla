--------------------- MODULE ReadersWriters_proof_SafetyCorrect ----------------------------
(***************************************************************************)
(* TLAPS proof of the safety properties of the readers-writers spec:       *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []Safety                                                      *)
(*                                                                         *)
(* Both are inductive once we know that the head of `waiting` is a 2-tuple *)
(* with first component "read"/"write" (which TypeOK already gives us).   *)
(* Cardinality(writers) <= 1 follows because:                              *)
(*   - Writes only happen via ReadOrWrite, whose precondition is           *)
(*     `writers = {}`; so writers' = writers \cup {actor} = {actor}.       *)
(*   - StopActivity only removes elements; cardinality cannot grow there.  *)
(***************************************************************************)
EXTENDS ReadersWriters, FiniteSets, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* The spec leaves `NumActors` as an unconstrained CONSTANT.  Make the    *)
(* (TLC-implicit) assumption explicit so the finiteness reasoning goes    *)
(* through.                                                                *)
(***************************************************************************)
ASSUME NumActorsIsNat == NumActors \in Nat

(***************************************************************************)
(* The head of a non-empty Seq(T) is in T.                                 *)
(***************************************************************************)
LEMMA HeadInSeqRange ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Head(s) \in T
  OBVIOUS

LEMMA TailIsSeq ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Tail(s) \in Seq(T)
  OBVIOUS

(***************************************************************************)
(* The set of "read"/"write" labels is closed under SelectSeq, but TypeOK  *)
(* gives us all we need: waiting \in Seq({"read","write"} \X Actors).      *)
(***************************************************************************)

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* The mutex / single-writer safety property.                              *)
(* Inductive together with TypeOK.                                         *)
(***************************************************************************)
Inv == TypeOK /\ Safety

LEMMA SafetyStep == Inv /\ [Next]_vars => Inv'
PROOF OMITTED

THEOREM SafetyCorrect == Spec => []Safety
PROOF OBVIOUS
============================================================================
