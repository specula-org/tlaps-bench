---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_InsertProposal ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_InsertProposalScaffold
THEOREM Pres_Bounded_InsertProposal ==
  ASSUME TypedIndInv, NEW p \in Corr, InsertProposal(p),
         UNCHANGED <<round, step, decision, locked_value, locked_round, valid_value, valid_round, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
