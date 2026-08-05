---- MODULE bcastByz_FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ----
EXTENDS bcastByz_FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLCDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==  
  IndInv_Unforg_NoBcast_TLC => FCConstraints
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
