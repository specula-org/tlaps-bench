-------------------------- MODULE HourClock_proof_HCini_Invariant --------------------------
(***************************************************************************)
(* TLAPS proof of the theorem stated in HourClock.tla.                     *)
(***************************************************************************)
EXTENDS HourClock, TLAPS

THEOREM HCini_Invariant == HC => []HCini
PROOF OBVIOUS

============================================================================
