---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_UponProposalInPrevoteOrCommitAndPrevote ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_UponProposalInPrevoteOrCommitAndPrevoteScaffold
THEOREM Pres_Bounded_UponProposalInPrevoteOrCommitAndPrevote ==
  ASSUME TypedIndInv, NEW p \in Corr,
         UponProposalInPrevoteOrCommitAndPrevote(p),
         UNCHANGED <<round, decision, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
