---- MODULE FlashWithMutex_MemDataCorrect ----
EXTENDS FlashWithMutex_MemDataCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM MemDataCorrect == Spec => []MemDataProp
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
