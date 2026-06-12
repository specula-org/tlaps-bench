--------------------------- MODULE ivy_examples_tlb_Liveness ---------------------------
EXTENDS IvyTlb

ProcessorMakesProgress(p) ==
  pc[p] \in {MainCheck, ResponderClearActionNeeded}

NonStarvation ==
  \A p \in Processor : TRUE ~> ProcessorMakesProgress(p)

THEOREM Liveness == Spec => NonStarvation
PROOF OBVIOUS

=============================================================================
