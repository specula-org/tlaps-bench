---- MODULE Sailfish_AgreementCorrect ----
EXTENDS Sailfish_AgreementCorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM AgreementCorrect == Spec => []Agreement
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
