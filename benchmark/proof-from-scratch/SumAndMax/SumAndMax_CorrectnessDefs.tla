----------------------------- MODULE SumAndMax_CorrectnessDefs -----------------------------
EXTENDS SumAndMaxModel

Correctness == pc = "Done" => sum =< N*max

=============================================================================

Writing algorithm and model checking: 15 min
Writing proof, before stopping to check for tlapm bug: 24 min
Writing proof: 12 min.
Writing proof: 12 min.
