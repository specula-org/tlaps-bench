---- MODULE PaxosProof_line91 ----
EXTENDS PaxosProof_line91Defs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM \A b \in Ballot, v \in Value : 
            Phase2a(b,v) /\ Inv => \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
