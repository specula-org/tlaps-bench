------------------------------ MODULE EuclidEx_PartialCorrectness ------------------------------
EXTENDS EuclidEx

PartialCorrectness ==
    (pc = "Done") => (x = y) /\ (x = GCD(M, N))

THEOREM Spec => []PartialCorrectness
PROOF OBVIOUS
=============================================================================

