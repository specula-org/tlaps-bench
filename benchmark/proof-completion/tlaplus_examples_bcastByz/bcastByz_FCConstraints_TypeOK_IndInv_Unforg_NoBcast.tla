---- MODULE bcastByz_FCConstraints_TypeOK_IndInv_Unforg_NoBcast ----
EXTENDS bcastByz_FCConstraints_TypeOK_IndInv_Unforg_NoBcastScaffold
THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast ==  
  IndInv_Unforg_NoBcast => FCConstraints /\ TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
