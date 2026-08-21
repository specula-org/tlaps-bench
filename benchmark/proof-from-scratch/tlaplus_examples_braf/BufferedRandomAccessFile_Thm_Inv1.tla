---- MODULE BufferedRandomAccessFile_Thm_Inv1 ----
EXTENDS BufferedRandomAccessFile_Thm_Inv1Defs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_Inv1 == Spec => []Inv1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
