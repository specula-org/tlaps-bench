---- MODULE bosco_Lemma4_0Correct ----
EXTENDS bosco_Lemma4_0CorrectDefs

LOCAL INSTANCE TLAPS
LOCAL NatInductionLib == INSTANCE NaturalsInduction
LOCAL FiniteSetTheoremsLib == INSTANCE FiniteSetTheorems
LOCAL WellFoundedInductionLib == INSTANCE WellFoundedInduction

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Lemma4_0Correct == Spec => []Lemma4_0
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
