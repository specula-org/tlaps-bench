---- MODULE FlashWithMutex_WbProgressCorrect ----
EXTENDS FlashWithMutex_WbProgressCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM WbProgressCorrect == FairSpec => WbProgress
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
