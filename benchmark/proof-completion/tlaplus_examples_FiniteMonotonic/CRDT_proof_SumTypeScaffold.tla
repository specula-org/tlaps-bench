------------------------------- MODULE CRDT_proof_SumTypeScaffold ---------------------------------
EXTENDS CRDT_proofModel

(***************************************************************************)
(* Proofs of safety properties.                                            *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM Safe == Spec => []Safety
PROOF OMITTED

THEOREM Spec => Monotonicity
PROOF OMITTED
(***************************************************************************)
(* Sum the values of a vector of natural numbers. We discharge the four    *)
(* Sum lemmas by reducing them to the corresponding `SumFunction` theorems *)
(* in the community-modules `FunctionTheorems`, via the trivial unfolding  *)
(*   Sum(f) = FoldFunction(+, 0, f)                                        *)
(*          = FoldFunctionOnSet(+, 0, f, DOMAIN f)                         *)
(*          = SumFunctionOnSet(f, DOMAIN f)                                *)
(*          = SumFunction(f).                                              *)
(***************************************************************************)
Sum(f) == FoldFunction(+, 0, f)

LEMMA SumIsSumFunction ==
  ASSUME NEW f
  PROVE  Sum(f) = SumFunction(f)
PROOF OMITTED

=============================================================================
