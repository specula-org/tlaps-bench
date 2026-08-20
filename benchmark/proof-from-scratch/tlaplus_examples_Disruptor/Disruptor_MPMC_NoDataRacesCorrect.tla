---- MODULE Disruptor_MPMC_NoDataRacesCorrect ----
EXTENDS Disruptor_MPMC_NoDataRacesCorrectDefs

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
