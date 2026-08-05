---- MODULE tendermint_single_indinv_proofs_PrevoteValueSenderSetCardinalityLeAllSenders ----
EXTENDS tendermint_single_indinv_proofs_PrevoteValueSenderSetCardinalityLeAllSendersScaffold
LEMMA PrevoteValueSenderSetCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
