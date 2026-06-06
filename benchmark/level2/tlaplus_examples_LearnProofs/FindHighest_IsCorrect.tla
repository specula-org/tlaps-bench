---------------------------- MODULE FindHighest_IsCorrect -----------------------------

EXTENDS FindHighest

Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

THEOREM IsCorrect == Spec => []Correctness
PROOF OBVIOUS

=============================================================================

