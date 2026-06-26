-------------------------- MODULE MajorityProof_PositionsType ------------------------------
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Proving type correctness is easy.                                       *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* Auxiliary lemmas about positions and occurrences.                       *)
(***************************************************************************)
LEMMA PositionsOne == \A v : PositionsBefore(v,1) = {}
PROOF OMITTED

LEMMA PositionsType == \A v, j : PositionsBefore(v,j) \in SUBSET (1 .. j-1)
PROOF OBVIOUS

(***************************************************************************)
(* We prove correctness based on the inductive invariant.                  *)
(***************************************************************************)

==============================================================================