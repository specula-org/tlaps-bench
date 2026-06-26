------------------------- MODULE KeyValueStore_proof_TypeAndLifecycle -----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM Spec => [](TypeInvariant /\ TxLifecycle)                      *)
(* stated in KeyValueStore.tla.                                            *)
(***************************************************************************)
EXTENDS KeyValueStore, TLAPS

Inv == TypeInvariant /\ TxLifecycle

THEOREM TypeAndLifecycle == Spec => []Inv
PROOF OBVIOUS

============================================================================
