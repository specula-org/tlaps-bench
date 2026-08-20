---- MODULE BufferedRandomAccessFile_Thm_SeekEstablishesInv2 ----
EXTENDS BufferedRandomAccessFile_Thm_SeekEstablishesInv2Defs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_SeekEstablishesInv2 == Spec => SeekEstablishesInv2
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
