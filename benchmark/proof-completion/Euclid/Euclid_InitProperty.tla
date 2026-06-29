-------------------- MODULE Euclid_InitProperty --------------------
EXTENDS Euclid

ResultCorrect == (x = y) => x = GCD(M, N)

InductiveInvariant ==
  /\ x \in Number
  /\ y \in Number
  /\ GCD(x, y) = GCD(M, N)
USE DEF Number

THEOREM InitProperty == Init => InductiveInvariant
PROOF OBVIOUS
=======================================================