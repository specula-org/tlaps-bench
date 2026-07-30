---- MODULE PaxosHistVar_SafeAtStable ----
EXTENDS PaxosHistVar_SafeAtStableScaffold
LEMMA SafeAtStable == Inv /\ Next => 
                          \A v \in Values, b \in Ballots:
                                  SafeAt(v, b) => SafeAt(v, b)'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
