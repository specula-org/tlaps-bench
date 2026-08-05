------------------------------- MODULE Peterson_IndInvariantDefs -------------------------------

EXTENDS PetersonModel

lockcs(i) ==
  pc[i] \in {"cs", "a4"}
Inv ==
  /\ \A p \in ProcSet : c[p] <=> pc[p] \in {"a2", "a3", "cs", "a4"}
  /\ \A p \in ProcSet : pc[p] \in {"cs", "a4"} 
      => (turn = p \/ pc[Other(p)] \in {"a0", "a1", "a2"})
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))

===============================================================================
