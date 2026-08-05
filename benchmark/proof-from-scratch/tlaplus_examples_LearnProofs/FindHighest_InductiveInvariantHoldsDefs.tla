---------------------------- MODULE FindHighest_InductiveInvariantHoldsDefs -----------------------------

EXTENDS FindHighestModel

InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

=============================================================================

