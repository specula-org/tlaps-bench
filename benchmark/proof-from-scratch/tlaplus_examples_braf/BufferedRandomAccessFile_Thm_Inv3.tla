---- MODULE BufferedRandomAccessFile_Thm_Inv3 ----
EXTENDS BufferedRandomAccessFile_Thm_Inv3Defs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_Inv3 == Spec => []Inv3
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
