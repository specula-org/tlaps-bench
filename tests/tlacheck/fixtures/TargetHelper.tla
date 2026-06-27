---- MODULE TargetHelper ----
EXTENDS Integers
LEMMA Helper == \A n \in Nat : n >= 0
PROOF OBVIOUS
THEOREM Goal == \A n \in Nat : n + 0 = n
PROOF BY Helper
====
