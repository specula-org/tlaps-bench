---- MODULE Consensus_LiveSpecEquals ----
EXTENDS Consensus_LiveSpecEqualsDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
