---- MODULE AtomicBakeryWithoutSMT_AfterPrime ----
EXTENDS AtomicBakeryWithoutSMT_AfterPrimeScaffold
THEOREM AfterPrime == 
  ASSUME NEW i, NEW j,
         After(i,j),
         UNCHANGED <<num[i], num[j], pc[i], unread[i], max[i]>>
  PROVE  After(i, j)'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
