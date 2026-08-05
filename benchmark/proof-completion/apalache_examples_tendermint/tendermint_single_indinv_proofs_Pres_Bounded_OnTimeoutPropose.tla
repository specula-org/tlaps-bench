---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_OnTimeoutPropose ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_OnTimeoutProposeScaffold
THEOREM Pres_Bounded_OnTimeoutPropose ==
  ASSUME TypedIndInv, NEW p \in Corr, OnTimeoutPropose(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
