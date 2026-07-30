---- MODULE EWD998PCal_proof_TypeOK_Step ----
EXTENDS EWD998PCal_proof_TypeOK_StepScaffold
USE NAssumption
LEMMA TypeOK_Step ==
  PCalTypeOK /\ [Next]_vars => PCalTypeOK'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
