---- MODULE tendermint_single_indinv_proofs_PrecommitLocksLaterPrevotesOp ----
EXTENDS tendermint_single_indinv_proofs_PrecommitLocksLaterPrevotesOpScaffold
LEMMA PrecommitLocksLaterPrevotesOp ==
  ASSUME IndTypeOk, PrecommitLocksLaterPrevotes,
         NEW p \in Corr, NEW r1 \in (0)..(MaxRound), NEW v \in ValidValues,
         NEW r2 \in (0)..(MaxRound), r2 > r1,
         \E pc \in msgs_precommit[r1] : p = pc.src /\ pc.id /= -1 /\ v /= pc.id,
         \E pv \in msgs_prevote[r2] : p = pv.src /\ v = pv.id
  PROVE  \E r \in {rr \in (0)..(MaxRound) : rr >= r1 /\ rr < r2} : Cardinality(PVSet(r, v)) >= 2 * T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
