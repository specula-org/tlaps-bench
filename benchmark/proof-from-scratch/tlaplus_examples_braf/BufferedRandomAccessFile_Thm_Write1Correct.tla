---- MODULE BufferedRandomAccessFile_Thm_Write1Correct ----
EXTENDS BufferedRandomAccessFile_Thm_Write1CorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_Write1Correct == Spec => Write1Correct
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
