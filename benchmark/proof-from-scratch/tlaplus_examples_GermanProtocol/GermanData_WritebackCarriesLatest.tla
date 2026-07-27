------------------------------ MODULE GermanData_WritebackCarriesLatest ------------------------------
EXTENDS GermanData

WritebackCarriesLatest ==
    \A i \in NODE :
        (chan3[i].cmd = "InvAck" /\ curCmd # "Empty" /\ exGntd = TRUE) =>
            /\ chan3[i].data = auxData
            /\ \A j \in NODE \ {i} :
                /\ cache[j].state # "E"
                /\ chan2[j].cmd # "GntE"
                /\ chan3[j].cmd # "InvAck"

THEOREM Spec => []WritebackCarriesLatest
PROOF OBVIOUS

=============================================================================
