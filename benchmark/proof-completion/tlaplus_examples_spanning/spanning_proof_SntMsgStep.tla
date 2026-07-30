---- MODULE spanning_proof_SntMsgStep ----
EXTENDS spanning_proof_SntMsgStepScaffold
LEMMA SntMsgStep == Inv /\ [Next]_vars => Inv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
