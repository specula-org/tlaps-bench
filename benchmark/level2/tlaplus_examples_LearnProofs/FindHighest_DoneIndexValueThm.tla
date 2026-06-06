---------------------------- MODULE FindHighest_DoneIndexValueThm -----------------------------

EXTENDS FindHighest

DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
PROOF OBVIOUS

=============================================================================

