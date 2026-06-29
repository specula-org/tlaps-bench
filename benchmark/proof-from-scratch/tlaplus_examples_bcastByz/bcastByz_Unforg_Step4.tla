------------------------------ MODULE bcastByz_Unforg_Step4 ------------------------------

EXTENDS bcastByz

Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC")) 

THEOREM Unforg_Step4 == SpecNoBcast => []Unforg
PROOF OBVIOUS
        
=============================================================================

