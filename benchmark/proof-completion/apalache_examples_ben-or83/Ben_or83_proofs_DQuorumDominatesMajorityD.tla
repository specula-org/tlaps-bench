---- MODULE Ben_or83_proofs_DQuorumDominatesMajorityD ----
EXTENDS Ben_or83_proofs_DQuorumDominatesMajorityDScaffold
THEOREM DQuorumDominatesMajorityD ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1,
         NEW w \in VALUES,
         2 * Cardinality(Senders2(DvSet(r, w))) > N + T
  PROVE  w = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
