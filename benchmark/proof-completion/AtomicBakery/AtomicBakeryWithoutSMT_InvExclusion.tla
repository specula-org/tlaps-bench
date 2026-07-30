---- MODULE AtomicBakeryWithoutSMT_InvExclusion ----
EXTENDS AtomicBakeryWithoutSMT_InvExclusionScaffold
THEOREM InvExclusion == Inv => MutualExclusion
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
