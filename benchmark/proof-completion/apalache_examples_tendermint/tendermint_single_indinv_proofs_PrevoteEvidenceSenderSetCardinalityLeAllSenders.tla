---- MODULE tendermint_single_indinv_proofs_PrevoteEvidenceSenderSetCardinalityLeAllSenders ----
EXTENDS tendermint_single_indinv_proofs_PrevoteEvidenceSenderSetCardinalityLeAllSendersScaffold
LEMMA PrevoteEvidenceSenderSetCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound), NEW E \in SUBSET msgs_prevote[r]
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in E : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
