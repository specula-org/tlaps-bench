------------------------- MODULE KeyValueStore_proof_TypeAndLifecycleScaffold -----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM Spec => [](TypeInvariant /\ TxLifecycle)                      *)
(* stated in KeyValueStore.tla.                                            *)
(***************************************************************************)
EXTENDS KeyValueStore, TLAPS

Inv == TypeInvariant /\ TxLifecycle

=============================================================================
