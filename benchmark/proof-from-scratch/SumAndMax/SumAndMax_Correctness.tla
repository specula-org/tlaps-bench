----------------------------- MODULE SumAndMax_Correctness -----------------------------
EXTENDS SumAndMax

Correctness == pc = "Done" => sum =< N*max

THEOREM Spec => []Correctness
PROOF OBVIOUS

=============================================================================

Writing algorithm and model checking: 15 min
Writing proof, before stopping to check for tlapm bug: 24 min
Writing proof: 12 min.
Writing proof: 12 min.
