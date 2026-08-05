---- MODULE tendermint_single_indinv_proofs_SubsetCFFinite ----
EXTENDS tendermint_single_indinv_proofs_SubsetCFFiniteScaffold
LEMMA SubsetCFFinite == ASSUME NEW A, A \subseteq (Corr \union Faulty) PROVE IsFiniteSet(A)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
