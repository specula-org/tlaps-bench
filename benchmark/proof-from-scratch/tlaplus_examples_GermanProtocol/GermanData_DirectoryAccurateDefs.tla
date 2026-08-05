------------------------------ MODULE GermanData_DirectoryAccurateDefs ------------------------------
EXTENDS GermanDataModel

DirectoryAccurate ==
    \A i \in NODE : cache[i].state \in {"S", "E"} => i \in shrSet

=============================================================================
