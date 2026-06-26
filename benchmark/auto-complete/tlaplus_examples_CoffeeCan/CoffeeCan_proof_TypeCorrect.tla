--------------------------- MODULE CoffeeCan_proof_TypeCorrect ----------------------------
(***************************************************************************)
(* TLAPS proof of  Spec => []TypeInvariant.                                *)
(*                                                                         *)
(* Strengthening: BeanCount \in 0..MaxBeanCount.  Each action decreases    *)
(* the total bean count by exactly 1, so the bound is preserved.           *)
(* Without the bound, PickSameColorWhite could push can.black past         *)
(* MaxBeanCount.                                                            *)
(***************************************************************************)
EXTENDS CoffeeCan, TLAPS

BeanBound == BeanCount \in 0 .. MaxBeanCount

Inv == TypeInvariant /\ BeanBound

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS
============================================================================
