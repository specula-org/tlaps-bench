---- MODULE FlashWithMutex_DirProgressCorrect ----
EXTENDS FlashWithMutex_DirProgressCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM DirProgressCorrect == FairSpec => DirProgress
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
