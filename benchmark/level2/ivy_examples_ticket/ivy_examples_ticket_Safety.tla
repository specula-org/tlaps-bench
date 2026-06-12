------------------------- MODULE ivy_examples_ticket_Safety -------------------------
EXTENDS IvyTicket

MutualExclusion ==
  \A t1, t2 \in Thread :
    (pc[t1] = "Critical" /\ pc[t2] = "Critical") => t1 = t2

THEOREM Safety == SafetySpec => []MutualExclusion
PROOF OBVIOUS

=============================================================================
