---------------- MODULE ivy_examples_hybrid_reliable_broadcast_cisa_Safety ----------------
EXTENDS IvyHybridReliableBroadcastCisa

Unforgeability ==
  (\E n \in Node : Obedient(n) /\ accept[n]) =>
  (\E m \in Node : Obedient(m) /\ m \in RcvInit)

THEOREM Safety == SafetySpec => []Unforgeability
PROOF OBVIOUS

=============================================================================
