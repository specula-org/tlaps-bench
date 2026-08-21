---- MODULE Disruptor_SPMC_NoDataRacesCorrect ----
EXTENDS Disruptor_SPMC_NoDataRacesCorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM NoDataRacesCorrect == Spec => []NoDataRaces
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
