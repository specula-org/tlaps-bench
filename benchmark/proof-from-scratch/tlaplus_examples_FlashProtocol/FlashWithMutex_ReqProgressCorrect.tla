---- MODULE FlashWithMutex_ReqProgressCorrect ----
EXTENDS FlashWithMutex_ReqProgressCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM ReqProgressCorrect == FairSpec => ReqProgress
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
