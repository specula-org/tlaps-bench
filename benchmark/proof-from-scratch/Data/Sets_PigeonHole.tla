---- MODULE Sets_PigeonHole ----
EXTENDS Sets_PigeonHoleDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
