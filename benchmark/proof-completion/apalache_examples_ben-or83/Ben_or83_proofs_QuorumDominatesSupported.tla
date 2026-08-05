---- MODULE Ben_or83_proofs_QuorumDominatesSupported ----
EXTENDS Ben_or83_proofs_QuorumDominatesSupportedScaffold
THEOREM QuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v),
         NEW w \in SupportedValues(r)
  PROVE  w = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
