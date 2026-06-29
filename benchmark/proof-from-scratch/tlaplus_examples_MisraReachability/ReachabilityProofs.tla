------------------------- MODULE ReachabilityProofs -------------------------

EXTENDS Reachability, NaturalsInduction, TLAPS

LEMMA Reachable0 ==
       \A S \in SUBSET Nodes : 
           \A n \in S : n \in ReachableFrom(S)

  PROOF OMITTED

LEMMA Reachable1 == 
        \A S, T \in SUBSET Nodes : 
          (\A n \in S : Succ[n] \subseteq (S \cup T))
            => (S \cup ReachableFrom(T)) = ReachableFrom(S \cup T)

  PROOF OMITTED

LEMMA Reachable2 == 
            \A S \in SUBSET Nodes: \A n \in S : 
                 /\ ReachableFrom(S) = ReachableFrom(S \cup Succ[n])
                 /\ n \in ReachableFrom(S)
  PROOF OMITTED

LEMMA Reachable3 ==  ReachableFrom({}) = {}
  PROOF OMITTED

=============================================================================

