------------------------------ MODULE bcastByz_Unforg_Step4Defs ------------------------------

EXTENDS bcastByzModel

Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC")) 

=============================================================================

