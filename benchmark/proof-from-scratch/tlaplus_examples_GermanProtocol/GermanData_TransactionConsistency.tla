------------------------------ MODULE GermanData_TransactionConsistency ------------------------------
EXTENDS GermanData

TransactionConsistency ==
    (curCmd = "Empty") <=> (curPtr = NoNode)

THEOREM Spec => []TransactionConsistency
PROOF OBVIOUS

=============================================================================
