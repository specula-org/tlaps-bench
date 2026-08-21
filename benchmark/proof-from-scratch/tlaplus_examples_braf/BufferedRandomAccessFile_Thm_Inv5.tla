---- MODULE BufferedRandomAccessFile_Thm_Inv5 ----
EXTENDS BufferedRandomAccessFile_Thm_Inv5Defs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_Inv5 == Spec => []Inv5
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
