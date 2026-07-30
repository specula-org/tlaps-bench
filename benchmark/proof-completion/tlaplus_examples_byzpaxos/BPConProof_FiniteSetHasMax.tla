---- MODULE BPConProof_FiniteSetHasMax ----
EXTENDS BPConProof_FiniteSetHasMaxScaffold
LEMMA FiniteSetHasMax ==
        ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), S # {}
        PROVE  \E max \in S : \A x \in S : max >= x
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
