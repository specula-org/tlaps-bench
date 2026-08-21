---- MODULE bosco_Lemma4_1Correct ----
EXTENDS bosco_Lemma4_1CorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Lemma4_1Correct == Spec => []Lemma4_1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
