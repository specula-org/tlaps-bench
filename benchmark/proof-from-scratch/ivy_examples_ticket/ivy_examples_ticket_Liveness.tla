------------------------- MODULE ivy_examples_ticket_Liveness -------------------------
EXTENDS IvyTicket

NonStarvation ==
  \A t \in Thread : (pc[t] = "Waiting") ~> (pc[t] = "Critical")

THEOREM Liveness == Spec => NonStarvation
PROOF OBVIOUS

=============================================================================
