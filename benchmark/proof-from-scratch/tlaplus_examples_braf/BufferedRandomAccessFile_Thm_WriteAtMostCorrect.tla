---- MODULE BufferedRandomAccessFile_Thm_WriteAtMostCorrect ----
EXTENDS BufferedRandomAccessFile_Thm_WriteAtMostCorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_WriteAtMostCorrect == Spec => WriteAtMostCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
