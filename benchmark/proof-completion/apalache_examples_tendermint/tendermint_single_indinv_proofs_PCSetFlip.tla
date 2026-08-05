---- MODULE tendermint_single_indinv_proofs_PCSetFlip ----
EXTENDS tendermint_single_indinv_proofs_PCSetFlipScaffold
LEMMA PCSetFlip ==
  ASSUME NEW r, NEW d
  PROVE  PCSet(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit[r] : d = mm.id} : s = m.src}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
