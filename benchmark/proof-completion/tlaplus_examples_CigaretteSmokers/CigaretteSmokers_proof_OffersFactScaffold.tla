--------------------- MODULE CigaretteSmokers_proof_OffersFactScaffold ---------------------------
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
THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* AtMostOne: at most one smoker is smoking.                               *)
(* Combined invariant with TypeOK (TypeOK is needed to type-check the     *)
(* set comprehension).                                                     *)
(***************************************************************************)
SmokingSet == {r \in Ingredients : smokers[r].smoking}

LEMMA SmokingSetFinite ==
  ASSUME TypeOK
  PROVE  /\ IsFiniteSet(SmokingSet)
         /\ Cardinality(SmokingSet) \in Nat
PROOF OMITTED

LEMMA AtMostOneViaSmokingSet == AtMostOne <=> Cardinality(SmokingSet) <= 1
PROOF OMITTED

(***************************************************************************)
(* The spec's unnamed ASSUME extracted as a fact for use in proofs.        *)
(***************************************************************************)
=============================================================================
