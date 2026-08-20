---- MODULE Peterson_Refinement ----
EXTENDS Peterson_RefinementDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Refinement == Spec => L!Spec
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
