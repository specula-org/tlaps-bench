---- MODULE TPaxosWithProof_MaxTypeOK ----
EXTENDS TPaxosWithProof_MaxTypeOKScaffold
LEMMA MaxTypeOK == \A a \in AllBallot, b \in Ballot: Max(a, b) \in Ballot
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
