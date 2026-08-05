---- MODULE tendermint_single_indinv_proofs_PrecommitsLockValueOp ----
EXTENDS tendermint_single_indinv_proofs_PrecommitsLockValueOpScaffold
LEMMA PrecommitsLockValueOp ==
  ASSUME IndTypeOk, PrecommitsLockValue
  PROVE  \A r0 \in (0)..(MaxRound), w \in ValidValues :
           \/ Cardinality(PCSet(r0, w)) < 2 * T + 1
           \/ \A r3 \in {x \in (0)..(MaxRound) : x > r0} : \A w2 \in (ValidValues \ {w}) :
                Cardinality(PVSet(r3, w2)) < 2 * T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
