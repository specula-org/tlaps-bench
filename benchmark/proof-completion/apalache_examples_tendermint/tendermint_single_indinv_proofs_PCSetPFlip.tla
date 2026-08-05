---- MODULE tendermint_single_indinv_proofs_PCSetPFlip ----
EXTENDS tendermint_single_indinv_proofs_PCSetPFlipScaffold
LEMMA PCSetPFlip ==
  ASSUME NEW r, NEW d
  PROVE  PCSetP(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit'[r] : d = mm.id} : s = m.src}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
