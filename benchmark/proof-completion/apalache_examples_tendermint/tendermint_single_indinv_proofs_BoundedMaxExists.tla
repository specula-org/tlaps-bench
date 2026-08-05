---- MODULE tendermint_single_indinv_proofs_BoundedMaxExists ----
EXTENDS tendermint_single_indinv_proofs_BoundedMaxExistsScaffold
LEMMA BoundedMaxExists ==
  ASSUME NEW b \in Nat, NEW S \in SUBSET (0)..b, S # {}
  PROVE  \E mx \in S : \A o \in S : mx >= o
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
