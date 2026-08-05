---- MODULE tendermint_single_indinv_proofs_PVSetPFlip ----
EXTENDS tendermint_single_indinv_proofs_PVSetPFlipScaffold
LEMMA PVSetPFlip ==
  ASSUME NEW r, NEW d
  PROVE  PVSetP(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote'[r] : d = mm.id} : s = m.src}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
