---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_UponQuorumOfPrevotesAny ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_UponQuorumOfPrevotesAnyScaffold
THEOREM Pres_Bounded_UponQuorumOfPrevotesAny ==
  ASSUME TypedIndInv, NEW p \in Corr, UponQuorumOfPrevotesAny(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
