---------------------- MODULE ivy_examples_ticket_nested_SafetyDefs ----------------------
EXTENDS ivy_examples_ticket_nestedModel

MutualExclusion ==
  \A t1, t2 \in Thread :
    (pc[t1] = "Critical" /\ pc[t2] = "Critical") => t1 = t2

=============================================================================
