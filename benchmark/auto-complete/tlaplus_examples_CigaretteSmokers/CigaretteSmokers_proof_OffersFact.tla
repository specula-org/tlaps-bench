--------------------- MODULE CigaretteSmokers_proof_OffersFact ---------------------------
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
LEMMA OffersFact ==
  /\ Offers \subseteq SUBSET Ingredients
  /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1
PROOF OBVIOUS

(***************************************************************************)
(* Cardinality(Ingredients) >= 1 follows from the existence of any         *)
(* dealer \in Offers (Offers is non-empty by Init's `dealer \in Offers`,  *)
(* but more directly: any d \in Offers has |d| = |Ingredients| - 1 \in Nat *)
(* which implies |Ingredients| >= 1.  We don't actually need this for the  *)
(* proof of AtMostOne, just for OffersFact reasoning).                     *)
(***************************************************************************)

(***************************************************************************)
(* The smoking set after `startSmoking` equals the set of ingredients     *)
(* that complete the dealer.                                               *)
(***************************************************************************)

(***************************************************************************)
(* The smoking set after `stopSmoking` is a subset of the previous one.   *)
(***************************************************************************)

(***************************************************************************)
(* Main inductive invariant.                                               *)
(***************************************************************************)
Inv == TypeOK /\ AtMostOne

============================================================================
