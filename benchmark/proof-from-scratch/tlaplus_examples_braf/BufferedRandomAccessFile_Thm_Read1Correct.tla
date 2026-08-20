---- MODULE BufferedRandomAccessFile_Thm_Read1Correct ----
EXTENDS BufferedRandomAccessFile_Thm_Read1CorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_Read1Correct == Spec => Read1Correct
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
