---------------- MODULE ivy_examples_hybrid_reliable_broadcast_cisa_SafetyDefs ----------------
EXTENDS ivy_examples_hybrid_reliable_broadcast_cisaModel

Unforgeability ==
  (\E n \in Node : Obedient(n) /\ accept[n]) =>
  (\E m \in Node : Obedient(m) /\ m \in RcvInit)

=============================================================================
