---------------------- MODULE ivy_examples_ticket_nested_Liveness ----------------------
EXTENDS IvyTicketNested

NonStarvation ==
  \A t \in Thread : (pc[t] = "Waiting") ~> (pc[t] = "Critical")

THEOREM Liveness == Spec => NonStarvation
PROOF OBVIOUS

=============================================================================
