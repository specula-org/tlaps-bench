---- MODULE Consensus_EnabledDef ----
EXTENDS Consensus_EnabledDefScaffold
LEMMA EnabledDef == (ENABLED <<Next>>_vars) <=> (chosen = {})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
