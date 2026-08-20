---- MODULE btree_TypeOkCorrect ----
EXTENDS btree_TypeOkCorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeOkCorrect == Spec => []TypeOk
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
