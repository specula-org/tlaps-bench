---- MODULE FlashWithMutex_InvProgressCorrect ----
EXTENDS FlashWithMutex_InvProgressCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM InvProgressCorrect == FairSpec => InvProgress
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
