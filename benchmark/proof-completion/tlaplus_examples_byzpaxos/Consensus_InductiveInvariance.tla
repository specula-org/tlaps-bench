---- MODULE Consensus_InductiveInvariance ----
EXTENDS Consensus_InductiveInvarianceScaffold
LEMMA InductiveInvariance ==
           Inv /\ [Next]_vars => Inv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
