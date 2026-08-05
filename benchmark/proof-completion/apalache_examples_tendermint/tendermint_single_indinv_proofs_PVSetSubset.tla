---- MODULE tendermint_single_indinv_proofs_PVSetSubset ----
EXTENDS tendermint_single_indinv_proofs_PVSetSubsetScaffold
LEMMA PVSetSubset == ASSUME NEW r, NEW d PROVE PVSet(r, d) \in SUBSET (Corr \union Faulty)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
