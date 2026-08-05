---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_UponQuorumOfPrecommitsAny ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_UponQuorumOfPrecommitsAnyScaffold
THEOREM Pres_Bounded_UponQuorumOfPrecommitsAny ==
  ASSUME TypedIndInv, NEW p \in Corr,
         UponQuorumOfPrecommitsAny(p),
         UNCHANGED <<decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
