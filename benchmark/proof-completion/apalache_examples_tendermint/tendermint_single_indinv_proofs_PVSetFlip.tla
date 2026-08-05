---- MODULE tendermint_single_indinv_proofs_PVSetFlip ----
EXTENDS tendermint_single_indinv_proofs_PVSetFlipScaffold
LEMMA PVSetFlip ==
  ASSUME NEW r, NEW d
  PROVE  PVSet(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote[r] : d = mm.id} : s = m.src}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
