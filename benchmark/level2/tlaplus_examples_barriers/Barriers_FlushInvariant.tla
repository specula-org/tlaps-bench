------------------------------- MODULE Barriers_FlushInvariant -------------------------------

EXTENDS Barriers

barrier1(p) ==
  pc[p] \in {"a0", "a1", "a2", "a3", "a4", "a5", "a6"}
ProcsInB1 ==
  {p \in ProcSet : barrier1(p)}
  
barrier2(p) ==
  pc[p] \in {"a7", "a8", "a9", "a10", "a11", "a12"}
ProcsInB2 ==
  {p \in ProcSet : barrier2(p)}

FlushInv ==
  /\ gate_1 > 0 => gate_1 = Cardinality(ProcsInB1)
  /\ gate_2 > 0 => gate_2 = Cardinality(ProcsInB2)

THEOREM FlushInvariant == Spec => []FlushInv
PROOF OBVIOUS
 
===============================================================================
