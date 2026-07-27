------------------------------ MODULE GermanData_DirectoryAccurate ------------------------------
EXTENDS GermanData

DirectoryAccurate ==
    \A i \in NODE : cache[i].state \in {"S", "E"} => i \in shrSet

THEOREM Spec => []DirectoryAccurate
PROOF OBVIOUS

=============================================================================
