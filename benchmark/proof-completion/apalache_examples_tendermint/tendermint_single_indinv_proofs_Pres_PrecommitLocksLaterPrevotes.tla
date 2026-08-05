---- MODULE tendermint_single_indinv_proofs_Pres_PrecommitLocksLaterPrevotes ----
EXTENDS tendermint_single_indinv_proofs_Pres_PrecommitLocksLaterPrevotesScaffold
THEOREM Pres_PrecommitLocksLaterPrevotes ==
  ASSUME TypedIndInv, Step PROVE PrecommitLocksLaterPrevotes'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
