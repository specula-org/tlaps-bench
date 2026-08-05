---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_UponProposalInPrecommitNoDecision ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_UponProposalInPrecommitNoDecisionScaffold
THEOREM Pres_Bounded_UponProposalInPrecommitNoDecision ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInPrecommitNoDecision(p),
         UNCHANGED <<round, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
