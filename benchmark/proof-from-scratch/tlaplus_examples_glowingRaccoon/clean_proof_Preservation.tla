---- MODULE clean_proof_Preservation ----
EXTENDS clean_proof_PreservationDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Preservation == Spec => []preservationInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
