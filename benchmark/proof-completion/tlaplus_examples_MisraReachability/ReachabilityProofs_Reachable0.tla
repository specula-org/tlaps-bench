---- MODULE ReachabilityProofs_Reachable0 ----
EXTENDS ReachabilityProofs_Reachable0Scaffold
LEMMA Reachable0 ==
       \A S \in SUBSET Nodes : 
           \A n \in S : n \in ReachableFrom(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
