------------------------------ MODULE GermanData_TransactionConsistencyDefs ------------------------------
EXTENDS GermanDataModel

TransactionConsistency ==
    (curCmd = "Empty") <=> (curPtr = NoNode)

=============================================================================
