------------------------- MODULE KeyValueStore_proof_TypeAndLifecycle -----------------------

EXTENDS KeyValueStore, TLAPS

Inv == TypeInvariant /\ TxLifecycle

THEOREM TypeAndLifecycle == Spec => []Inv
PROOF OBVIOUS

============================================================================
