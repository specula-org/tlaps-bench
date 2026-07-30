---- MODULE Paxos_SafeAtStable ----
EXTENDS Paxos_SafeAtStableScaffold
LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' => 
                          \A v \in Values, b \in Ballots:
                                  SafeAt(v, b) => SafeAt(v, b)'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
