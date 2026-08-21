---- MODULE Disruptor_SPMC_TypeOkCorrect ----
EXTENDS Disruptor_SPMC_TypeOkCorrectDefs

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
