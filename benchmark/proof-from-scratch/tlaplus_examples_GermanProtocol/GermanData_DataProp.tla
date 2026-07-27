------------------------------ MODULE GermanData_DataProp ------------------------------
EXTENDS GermanData

DataProp ==
    /\ (exGntd = FALSE => memData = auxData)
    /\ \A i \in NODE : cache[i].state # "I" => cache[i].data = auxData

THEOREM Spec => []DataProp
PROOF OBVIOUS

=============================================================================
