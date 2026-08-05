------------------------- MODULE KeyValueStore_proof_TypeAndLifecycleDefs -----------------------

EXTENDS KeyValueStore, TLAPS

Inv == TypeInvariant /\ TxLifecycle

============================================================================
