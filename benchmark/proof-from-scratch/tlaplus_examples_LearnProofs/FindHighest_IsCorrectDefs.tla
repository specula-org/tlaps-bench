---------------------------- MODULE FindHighest_IsCorrectDefs -----------------------------

EXTENDS FindHighestModel

Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

=============================================================================

