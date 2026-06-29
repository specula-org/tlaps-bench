-------------------- MODULE Euclid_Correctness --------------------
EXTENDS Euclid

ResultCorrect == (x = y) => x = GCD(M, N)

InductiveInvariant ==
  /\ x \in Number
  /\ y \in Number
  /\ GCD(x, y) = GCD(M, N)
USE DEF Number

THEOREM InitProperty == Init => InductiveInvariant
PROOF OMITTED
THEOREM NextProperty == InductiveInvariant /\ Next => InductiveInvariant'
PROOF OMITTED
THEOREM Correctness == Spec => []ResultCorrect
PROOF OBVIOUS
=======================================================