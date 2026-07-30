---- MODULE AtomicBakeryWithoutSMT_GGIrreflexive ----
EXTENDS AtomicBakeryWithoutSMT_GGIrreflexiveScaffold
THEOREM GGIrreflexive == ASSUME NEW i \in P,
                                NEW j \in P,
                                i # j,
                                num[i] \in Nat,
                                num[j] \in Nat
                         PROVE  ~ (GG(i, j) /\ GG(j, i))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
