---- MODULE BufferedRandomAccessFile_Thm_Safety ----
EXTENDS BufferedRandomAccessFile_Thm_SafetyDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_Safety == Spec => Safety
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
