------------------------------ MODULE GermanData_ExclusiveIsolation ------------------------------
EXTENDS GermanData

ExclusiveIsolation ==
    \A i \in NODE :
        cache[i].state = "E" =>
            /\ exGntd = TRUE
            /\ \A j \in NODE \ {i} :
                /\ cache[j].state = "I"
                /\ chan2[j].cmd \notin {"GntS", "GntE"}
                /\ chan3[j].cmd # "InvAck"

THEOREM Spec => []ExclusiveIsolation
PROOF OBVIOUS

=============================================================================
