---- MODULE BPConProof_FiniteMsgsLemma ----
EXTENDS BPConProof_FiniteMsgsLemmaScaffold
LEMMA FiniteMsgsLemma ==
        ASSUME NEW m, bmsgsFinite, bmsgs' = bmsgs \cup {m}
        PROVE  bmsgsFinite'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
