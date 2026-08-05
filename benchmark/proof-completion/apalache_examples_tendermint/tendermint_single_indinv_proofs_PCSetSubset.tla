---- MODULE tendermint_single_indinv_proofs_PCSetSubset ----
EXTENDS tendermint_single_indinv_proofs_PCSetSubsetScaffold
LEMMA PCSetSubset == ASSUME NEW r, NEW d PROVE PCSet(r, d) \in SUBSET (Corr \union Faulty)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
