---- MODULE EWD998_proof_B0NoMessagePending ----
EXTENDS EWD998_proof_B0NoMessagePendingScaffold
USE NAssumption
LEMMA B0NoMessagePending == 
  /\ TypeOK /\ B=0 => \A i \in Node : pending[i] = 0
  /\ TypeOK' /\ B'=0 => \A i \in Node : pending'[i] = 0
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
