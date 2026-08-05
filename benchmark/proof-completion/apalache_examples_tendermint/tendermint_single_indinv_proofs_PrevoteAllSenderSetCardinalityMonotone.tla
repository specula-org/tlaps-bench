---- MODULE tendermint_single_indinv_proofs_PrevoteAllSenderSetCardinalityMonotone ----
EXTENDS tendermint_single_indinv_proofs_PrevoteAllSenderSetCardinalityMonotoneScaffold
LEMMA PrevoteAllSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote'[r] : s = m.src})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
