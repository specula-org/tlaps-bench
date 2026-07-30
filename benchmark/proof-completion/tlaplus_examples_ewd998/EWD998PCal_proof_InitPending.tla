---- MODULE EWD998PCal_proof_InitPending ----
EXTENDS EWD998PCal_proof_InitPendingScaffold
USE NAssumption
LEMMA InitPending == Init => pending = [i \in Node |-> 0]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
