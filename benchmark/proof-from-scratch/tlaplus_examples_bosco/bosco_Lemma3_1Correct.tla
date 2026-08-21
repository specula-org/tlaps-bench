---- MODULE bosco_Lemma3_1Correct ----
EXTENDS bosco_Lemma3_1CorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Lemma3_1Correct == Spec => []Lemma3_1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
