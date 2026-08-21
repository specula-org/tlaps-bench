---- MODULE BufferedRandomAccessFile_Thm_Inv4 ----
EXTENDS BufferedRandomAccessFile_Thm_Inv4Defs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_Inv4 == Spec => []Inv4
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
