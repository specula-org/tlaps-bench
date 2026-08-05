---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_UponProposalInProposeAndPrevote ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_UponProposalInProposeAndPrevoteScaffold
THEOREM Pres_Bounded_UponProposalInProposeAndPrevote ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInProposeAndPrevote(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
