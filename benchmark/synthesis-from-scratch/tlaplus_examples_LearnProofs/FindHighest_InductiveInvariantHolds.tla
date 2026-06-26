---------------------------- MODULE FindHighest_InductiveInvariantHolds -----------------------------

EXTENDS FindHighest

InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF OBVIOUS

=============================================================================

