---- MODULE FlashWithMutex_CacheStateCorrect ----
EXTENDS FlashWithMutex_CacheStateCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM CacheStateCorrect == Spec => []CacheStateProp
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
