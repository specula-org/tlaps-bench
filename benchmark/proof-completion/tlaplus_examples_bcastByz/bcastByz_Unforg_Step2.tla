---- MODULE bcastByz_Unforg_Step2 ----
EXTENDS bcastByz_Unforg_Step2Scaffold
THEOREM Unforg_Step2 == IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
