---- MODULE TPaxosWithProof_NoneNotAValue ----
EXTENDS TPaxosWithProof_NoneNotAValueScaffold
LEMMA NoneNotAValue == None \notin Value
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
