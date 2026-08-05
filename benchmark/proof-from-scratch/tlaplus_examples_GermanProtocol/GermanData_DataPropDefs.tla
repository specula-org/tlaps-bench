------------------------------ MODULE GermanData_DataPropDefs ------------------------------
EXTENDS GermanDataModel

DataProp ==
    /\ (exGntd = FALSE => memData = auxData)
    /\ \A i \in NODE : cache[i].state # "I" => cache[i].data = auxData

=============================================================================
