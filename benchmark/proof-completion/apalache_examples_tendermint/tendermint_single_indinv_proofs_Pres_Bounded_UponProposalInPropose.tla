---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_UponProposalInPropose ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_UponProposalInProposeScaffold
THEOREM Pres_Bounded_UponProposalInPropose ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInPropose(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
