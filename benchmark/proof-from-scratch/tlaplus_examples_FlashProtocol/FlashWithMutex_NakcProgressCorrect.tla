---- MODULE FlashWithMutex_NakcProgressCorrect ----
EXTENDS FlashWithMutex_NakcProgressCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM NakcProgressCorrect == FairSpec => NakcProgress
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
