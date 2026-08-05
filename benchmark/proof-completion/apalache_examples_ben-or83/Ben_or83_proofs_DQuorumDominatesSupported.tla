---- MODULE Ben_or83_proofs_DQuorumDominatesSupported ----
EXTENDS Ben_or83_proofs_DQuorumDominatesSupportedScaffold
THEOREM DQuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1,
         NEW w \in SupportedValues(r)
  PROVE  w = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
