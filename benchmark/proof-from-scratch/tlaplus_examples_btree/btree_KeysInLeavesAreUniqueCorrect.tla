---- MODULE btree_KeysInLeavesAreUniqueCorrect ----
EXTENDS btree_KeysInLeavesAreUniqueCorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM KeysInLeavesAreUniqueCorrect == Spec => []KeysInLeavesAreUnique
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
