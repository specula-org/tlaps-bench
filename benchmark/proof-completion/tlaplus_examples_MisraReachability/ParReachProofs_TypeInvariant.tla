--------------------------- MODULE ParReachProofs_TypeInvariant ---------------------------
(***************************************************************************)
(* This module contains TLAPS checked proofs of the safety properties      *)
(* asserted in module ParReach--namely, the invariance of Inv and that the *)
(* parallel algorithm implements the safety part of Misra's algorithm under *)
(* the refinement mapping defined there.                                   *)
(***************************************************************************)
EXTENDS ParReach, Integers, TLAPS

LEMMA TypeInvariant == Spec  => []Inv
PROOF OBVIOUS

=============================================================================
\* Modification History
\* Last modified Sun Apr 14 16:55:36 PDT 2019 by lamport
\* Created Sat Apr 13 14:37:54 PDT 2019 by lamport
