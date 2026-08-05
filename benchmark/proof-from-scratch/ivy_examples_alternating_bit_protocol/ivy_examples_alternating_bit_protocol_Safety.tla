---- MODULE ivy_examples_alternating_bit_protocol_Safety ----
EXTENDS ivy_examples_alternating_bit_protocol_SafetyDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Safety == SafetySpec => []ReceiverValuesFromSender
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
