---- MODULE tendermint_single_indinv_proofs_Pres_AllValidAndLockedRoundBounded ----
EXTENDS tendermint_single_indinv_proofs_Pres_AllValidAndLockedRoundBoundedScaffold
THEOREM Pres_AllValidAndLockedRoundBounded ==
  ASSUME TypedIndInv, Step
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
