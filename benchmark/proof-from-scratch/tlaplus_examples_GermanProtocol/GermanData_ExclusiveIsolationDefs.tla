------------------------------ MODULE GermanData_ExclusiveIsolationDefs ------------------------------
EXTENDS GermanDataModel

ExclusiveIsolation ==
    \A i \in NODE :
        cache[i].state = "E" =>
            /\ exGntd = TRUE
            /\ \A j \in NODE \ {i} :
                /\ cache[j].state = "I"
                /\ chan2[j].cmd \notin {"GntS", "GntE"}
                /\ chan3[j].cmd # "InvAck"

=============================================================================
