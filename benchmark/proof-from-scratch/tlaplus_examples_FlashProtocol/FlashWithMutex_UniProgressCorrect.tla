---- MODULE FlashWithMutex_UniProgressCorrect ----
EXTENDS FlashWithMutex_UniProgressCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM UniProgressCorrect == FairSpec => UniProgress
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
