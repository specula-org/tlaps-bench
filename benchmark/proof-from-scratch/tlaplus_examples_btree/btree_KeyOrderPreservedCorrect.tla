---- MODULE btree_KeyOrderPreservedCorrect ----
EXTENDS btree_KeyOrderPreservedCorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM KeyOrderPreservedCorrect == Spec => []KeyOrderPreserved
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
