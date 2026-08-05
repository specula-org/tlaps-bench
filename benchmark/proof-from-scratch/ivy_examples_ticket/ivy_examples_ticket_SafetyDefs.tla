------------------------- MODULE ivy_examples_ticket_SafetyDefs -------------------------
EXTENDS ivy_examples_ticketModel

MutualExclusion ==
  \A t1, t2 \in Thread :
    (pc[t1] = "Critical" /\ pc[t2] = "Critical") => t1 = t2

=============================================================================
