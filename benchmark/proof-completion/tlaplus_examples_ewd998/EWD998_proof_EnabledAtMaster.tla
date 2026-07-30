---- MODULE EWD998_proof_EnabledAtMaster ----
EXTENDS EWD998_proof_EnabledAtMasterScaffold
USE NAssumption
COROLLARY EnabledAtMaster ==
  ASSUME TypeOK, Inv, Termination, token.pos = 0, ~ terminationDetected
  PROVE  ENABLED <<System>>_vars
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
