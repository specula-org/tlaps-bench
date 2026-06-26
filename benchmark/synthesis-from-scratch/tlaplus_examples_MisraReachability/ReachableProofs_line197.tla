-------------------------- MODULE ReachableProofs_line197 --------------------------

EXTENDS Reachable, ReachabilityProofs, TLAPS

THEOREM Spec => []((pc = "Done") => (marked = Reachable))

PROOF OBVIOUS
=============================================================================

