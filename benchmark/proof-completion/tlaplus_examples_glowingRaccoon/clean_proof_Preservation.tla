---- MODULE clean_proof_Preservation ----
EXTENDS clean_proof_PreservationScaffold
THEOREM Preservation == Spec => []preservationInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
