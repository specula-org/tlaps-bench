---- MODULE tendermint_single_indinv_proofs_PrecommitLockContra ----
EXTENDS tendermint_single_indinv_proofs_PrecommitLockContraScaffold
LEMMA PrecommitLockContra ==
  ASSUME TypedIndInv,
         NEW c \in Corr, NEW r0 \in (0)..(MaxRound), NEW r \in (0)..(MaxRound), r > r0,
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         \E pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w,
         \E pv \in msgs_prevote[r] : pv.src = c /\ pv.id = w2,
         Cardinality(PCSet(r0, w)) >= 2 * T + 1
  PROVE  FALSE
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
