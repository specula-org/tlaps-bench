------------------------------- MODULE EWD840_TerminationDetection -------------------------------
EXTENDS EWD840

terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

THEOREM Spec => []TerminationDetection
PROOF OBVIOUS

=============================================================================

