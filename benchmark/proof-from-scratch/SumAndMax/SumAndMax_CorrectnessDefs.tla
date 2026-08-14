----------------------------- MODULE SumAndMax_CorrectnessDefs -----------------------------
EXTENDS SumAndMaxModel

Correctness == pc = "Done" => sum =< N*max

=============================================================================
