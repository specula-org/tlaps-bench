---- MODULE ivy_examples_hybrid_reliable_broadcast_cisa_RelayLiveness ----
EXTENDS ivy_examples_hybrid_reliable_broadcast_cisa_RelayLivenessDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM RelayLiveness == Spec => Relay
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
