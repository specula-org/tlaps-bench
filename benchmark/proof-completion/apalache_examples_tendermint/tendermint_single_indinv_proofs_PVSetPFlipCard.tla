---- MODULE tendermint_single_indinv_proofs_PVSetPFlipCard ----
EXTENDS tendermint_single_indinv_proofs_PVSetPFlipCardScaffold
LEMMA PVSetPFlipCard ==
  ASSUME NEW r, NEW d
  PROVE  Cardinality(PVSetP(r, d)) =
           Cardinality({s \in (Corr \union Faulty) :
             \E pv0 \in {pp \in msgs_prevote'[r] : d = pp.id} : s = pv0.src})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
