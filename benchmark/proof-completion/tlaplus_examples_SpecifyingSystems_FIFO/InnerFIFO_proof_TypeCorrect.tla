------------------------- MODULE InnerFIFO_proof_TypeCorrect ---------------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM Spec => []TypeInvariant                                       *)
(* stated in InnerFIFO.tla.                                                *)
(***************************************************************************)
EXTENDS InnerFIFO, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

============================================================================
