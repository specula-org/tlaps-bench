---- MODULE ReachabilityProofs_Reachable2 ----
EXTENDS ReachabilityProofs_Reachable2Scaffold
LEMMA Reachable2 == 
            \A S \in SUBSET Nodes: \A n \in S : 
                 /\ ReachableFrom(S) = ReachableFrom(S \cup Succ[n])
                 /\ n \in ReachableFrom(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
