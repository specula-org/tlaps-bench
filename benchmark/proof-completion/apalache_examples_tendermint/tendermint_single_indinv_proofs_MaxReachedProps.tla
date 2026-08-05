---- MODULE tendermint_single_indinv_proofs_MaxReachedProps ----
EXTENDS tendermint_single_indinv_proofs_MaxReachedPropsScaffold
LEMMA MaxReachedProps ==
  ASSUME NEW rd, \A k \in DOMAIN rd : rd[k] \in (0)..(MaxRound)
  PROVE  /\ MaxReachedOf(rd) \in MaxCandOf(rd)
         /\ \A o \in MaxCandOf(rd) : MaxReachedOf(rd) >= o
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
