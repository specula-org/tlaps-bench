---- MODULE Barriers_BarrierExclusion ----
EXTENDS Barriers_BarrierExclusionDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM BarrierExclusion ==
    Inv => \/ ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
           \/ ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
