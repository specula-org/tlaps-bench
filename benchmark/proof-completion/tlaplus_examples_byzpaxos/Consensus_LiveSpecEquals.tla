---- MODULE Consensus_LiveSpecEquals ----
EXTENDS Consensus_LiveSpecEqualsScaffold
THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
