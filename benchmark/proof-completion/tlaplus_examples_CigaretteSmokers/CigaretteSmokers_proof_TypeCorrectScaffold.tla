--------------------- MODULE CigaretteSmokers_proof_TypeCorrectScaffold ---------------------------
(***************************************************************************)
(* TLAPS proofs of                                                         *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []AtMostOne                                                   *)
(*                                                                         *)
(* AtMostOne (at most one smoker is smoking) is inductive together with    *)
(* TypeOK once we know `Ingredients` is finite.                            *)
(***************************************************************************)
EXTENDS CigaretteSmokers, FiniteSets, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Ingredients is implicitly finite: the spec uses Cardinality on it.      *)
(***************************************************************************)
ASSUME IngredientsFinite == IsFiniteSet(Ingredients)

(***************************************************************************)
(* Type correctness.  The dealer disjunct dealer \in Offers \/ dealer = {} *)
(* is preserved trivially since both actions either set dealer to {} or    *)
(* nondeterministically choose dealer' \in Offers.                         *)
(***************************************************************************)
=============================================================================
