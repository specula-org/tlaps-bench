---- MODULE AtomicBakeryWithoutSMT_InitImpliesTypeOK ----
EXTENDS AtomicBakeryWithoutSMT_InitImpliesTypeOKScaffold
THEOREM InitImpliesTypeOK == 
  ASSUME Init
  PROVE  TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
