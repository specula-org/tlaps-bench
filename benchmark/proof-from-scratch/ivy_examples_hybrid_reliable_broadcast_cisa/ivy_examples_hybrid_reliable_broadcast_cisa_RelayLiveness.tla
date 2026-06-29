---------------- MODULE ivy_examples_hybrid_reliable_broadcast_cisa_RelayLiveness ----------------
EXTENDS IvyHybridReliableBroadcastCisa

SomeObedientAccepts ==
  \E n \in Node : Obedient(n) /\ accept[n]

AllCorrectAccept ==
  \A n \in Node : Correct(n) => accept[n]

Relay ==
  <>SomeObedientAccepts => <>AllCorrectAccept

THEOREM RelayLiveness == Spec => Relay
PROOF OBVIOUS

=============================================================================
