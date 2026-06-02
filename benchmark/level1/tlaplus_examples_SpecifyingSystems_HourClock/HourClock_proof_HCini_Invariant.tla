---- MODULE HourClock_proof_HCini_Invariant ----
EXTENDS Naturals, TLAPS
(* ---- Content from module HourClock ---- *)
VARIABLE hr
HCini  ==  hr \in (1 .. 12)
HCnxt  ==  hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC  ==  HCini /\ [][HCnxt]_hr
--------------------------------------------------------------
THEOREM  HC => []HCini

(***************************************************************************)
(* TLAPS proof of the theorem stated in HourClock.tla.                     *)
(***************************************************************************)

THEOREM HCini_Invariant == HC => []HCini
PROOF OBVIOUS

========================================