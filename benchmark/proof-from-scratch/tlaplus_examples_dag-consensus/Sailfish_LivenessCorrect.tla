---- MODULE Sailfish_LivenessCorrect ----
EXTENDS Sailfish_LivenessCorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM LivenessCorrect == Spec => []Liveness
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
