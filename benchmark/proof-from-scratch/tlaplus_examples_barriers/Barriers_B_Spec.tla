------------------------------- MODULE Barriers_B_Spec -------------------------------

EXTENDS Barriers

pc_translation(self) ==
  IF pc[self] \in {"a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8", "a9", "a10"}
    THEN "b1"
  ELSE IF pc[self] = "a0" 
    THEN "b0"
  ELSE IF gate_2 > 0
    THEN "b0"
  ELSE "b1"

B == INSTANCE Barrier WITH pc <- [p \in ProcSet |-> pc_translation(p)]

THEOREM Spec => B!Spec
PROOF OBVIOUS
===============================================================================
