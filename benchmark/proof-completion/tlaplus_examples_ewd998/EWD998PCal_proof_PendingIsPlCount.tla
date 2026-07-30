---- MODULE EWD998PCal_proof_PendingIsPlCount ----
EXTENDS EWD998PCal_proof_PendingIsPlCountScaffold
USE NAssumption
LEMMA PendingIsPlCount ==
  pending = [n \in Node |-> PlCount(network[n])]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
