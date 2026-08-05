---- MODULE FlashWithMutex_CacheDataCorrect ----
EXTENDS FlashWithMutex_CacheDataCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM CacheDataCorrect == Spec => []CacheDataProp
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
