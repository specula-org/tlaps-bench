---- MODULE EWD998PCal_proof_InitToken ----
EXTENDS EWD998PCal_proof_InitTokenScaffold
USE NAssumption
LEMMA InitToken == Init => token = [pos |-> 0, q |-> 0, color |-> "black"]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
