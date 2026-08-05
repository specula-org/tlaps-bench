---- MODULE tendermint_single_indinv_proofs_Inductive ----
EXTENDS tendermint_single_indinv_proofs_InductiveScaffold
THEOREM Inductive ==
  ASSUME TypedIndInv, Step
  PROVE  TypedIndInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
