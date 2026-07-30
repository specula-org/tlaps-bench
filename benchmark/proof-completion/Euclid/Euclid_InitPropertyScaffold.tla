-------------------- MODULE Euclid_InitPropertyScaffold --------------------
EXTENDS EuclidModel

ResultCorrect == (x = y) => x = GCD(M, N)

InductiveInvariant ==
  /\ x \in Number
  /\ y \in Number
  /\ GCD(x, y) = GCD(M, N)

=============================================================================
