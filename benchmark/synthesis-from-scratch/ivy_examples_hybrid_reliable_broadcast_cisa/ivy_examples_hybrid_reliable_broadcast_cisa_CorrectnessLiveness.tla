---------------- MODULE ivy_examples_hybrid_reliable_broadcast_cisa_CorrectnessLiveness ----------------
EXTENDS IvyHybridReliableBroadcastCisa

AllObedientInit ==
  \A n \in Node : Obedient(n) => n \in RcvInit

SomeCorrectAccepts ==
  \E n \in Node : Correct(n) /\ accept[n]

Correctness ==
  AllObedientInit => <>SomeCorrectAccepts

THEOREM CorrectnessLiveness == Spec => Correctness
PROOF OBVIOUS

=============================================================================
