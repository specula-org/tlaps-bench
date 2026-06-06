-------------------- MODULE Euclid_Correctness --------------------
EXTENDS Euclid

ResultCorrect == (x = y) => x = GCD(M, N)

USE DEF Number

THEOREM Correctness == Spec => []ResultCorrect
PROOF OBVIOUS
=======================================================