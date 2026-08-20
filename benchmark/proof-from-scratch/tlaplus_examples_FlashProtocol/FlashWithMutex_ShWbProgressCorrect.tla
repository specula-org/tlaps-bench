---- MODULE FlashWithMutex_ShWbProgressCorrect ----
EXTENDS FlashWithMutex_ShWbProgressCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM ShWbProgressCorrect == FairSpec => ShWbProgress
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
