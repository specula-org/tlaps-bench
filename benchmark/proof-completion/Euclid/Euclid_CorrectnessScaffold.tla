-------------------- MODULE Euclid_CorrectnessScaffold --------------------
EXTENDS EuclidModel_2

ResultCorrect == (x = y) => x = GCD(M, N)

InductiveInvariant ==
  /\ x \in Number
  /\ y \in Number
  /\ GCD(x, y) = GCD(M, N)

THEOREM InitProperty == Init => InductiveInvariant
PROOF OMITTED
THEOREM NextProperty == InductiveInvariant /\ Next => InductiveInvariant'
PROOF OMITTED
=============================================================================
