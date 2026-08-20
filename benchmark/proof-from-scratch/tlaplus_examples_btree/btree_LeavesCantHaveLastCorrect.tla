---- MODULE btree_LeavesCantHaveLastCorrect ----
EXTENDS btree_LeavesCantHaveLastCorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM LeavesCantHaveLastCorrect == Spec => []LeavesCantHaveLast
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
