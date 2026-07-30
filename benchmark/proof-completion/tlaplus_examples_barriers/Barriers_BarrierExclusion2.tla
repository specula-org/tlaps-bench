---- MODULE Barriers_BarrierExclusion2 ----
EXTENDS Barriers_BarrierExclusion2Scaffold
THEOREM BarrierExclusion2 ==
    TypeOK /\ Inv => 
      \/ (\A p \in ProcSet: pc[p] \in 
                    {"a5", "a6", "a7", "a8", "a9", "a10", "a11", "a12"})
      \/ (\A p \in ProcSet: pc[p] \in 
                    {"a11", "a12", "a0", "a1", "a2", "a3", "a4", "a5", "a6"})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
