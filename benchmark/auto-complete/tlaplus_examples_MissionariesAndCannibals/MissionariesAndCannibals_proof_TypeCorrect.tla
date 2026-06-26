--------------------- MODULE MissionariesAndCannibals_proof_TypeCorrect ------------------
(***************************************************************************)
(* TLAPS proof of  Spec => []TypeOK.                                       *)
(* (Solution is meant to be violated to find a solution; not a real        *)
(*  safety property.)                                                       *)
(***************************************************************************)
EXTENDS MissionariesAndCannibals_proof

(***************************************************************************)
(* The spec doesn't have a Spec operator -- it's only Init /\ [][Next]_... *)
(* implicitly via the .cfg.  We define it here for the proof.              *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS
============================================================================
