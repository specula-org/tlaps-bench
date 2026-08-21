---- MODULE Disruptor_MPMC_TypeOkCorrect ----
EXTENDS Disruptor_MPMC_TypeOkCorrectDefs

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
