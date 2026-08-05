---------------------------- MODULE FindHighest_TypeInvariantHoldsDefs -----------------------------

EXTENDS FindHighestModel

TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1..(Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}

=============================================================================

