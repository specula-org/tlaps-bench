---- MODULE BufferedRandomAccessFile_Thm_Inv2CanAlwaysBeRestored ----
EXTENDS BufferedRandomAccessFile_Thm_Inv2CanAlwaysBeRestoredDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Thm_Inv2CanAlwaysBeRestored == Spec => Inv2CanAlwaysBeRestored
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
