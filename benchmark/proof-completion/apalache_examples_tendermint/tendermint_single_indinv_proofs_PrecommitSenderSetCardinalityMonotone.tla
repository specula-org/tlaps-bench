---- MODULE tendermint_single_indinv_proofs_PrecommitSenderSetCardinalityMonotone ----
EXTENDS tendermint_single_indinv_proofs_PrecommitSenderSetCardinalityMonotoneScaffold
LEMMA PrecommitSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit'[r] : mm.id = idv} : s = m.src})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
