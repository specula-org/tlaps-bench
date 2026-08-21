---- MODULE bosco_Lemma3_0Correct ----
EXTENDS bosco_Lemma3_0CorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Lemma3_0Correct == Spec => []Lemma3_0
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
