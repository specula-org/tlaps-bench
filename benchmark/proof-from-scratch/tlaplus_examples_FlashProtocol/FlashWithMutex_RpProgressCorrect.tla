---- MODULE FlashWithMutex_RpProgressCorrect ----
EXTENDS FlashWithMutex_RpProgressCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM RpProgressCorrect == FairSpec => RpProgress
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
