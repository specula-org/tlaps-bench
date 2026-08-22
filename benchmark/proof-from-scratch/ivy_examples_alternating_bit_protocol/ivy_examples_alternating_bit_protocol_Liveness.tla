---- MODULE ivy_examples_alternating_bit_protocol_Liveness ----
EXTENDS ivy_examples_alternating_bit_protocol_LivenessDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Liveness == Spec => DataDelivery
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
