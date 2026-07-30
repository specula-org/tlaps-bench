---- MODULE TPaxosWithProof_SafeAtStable ----
EXTENDS TPaxosWithProof_SafeAtStableScaffold
LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' =>
                            \A v \in Value, b \in Ballot:
                               SafeAt(b, v) => SafeAt(b, v)'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
