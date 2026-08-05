---- MODULE Ben_or83_proofs_QuorumUnique ----
EXTENDS Ben_or83_proofs_QuorumUniqueScaffold
THEOREM QuorumUnique ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, NEW w \in VALUES,
         ExistsQuorum2LessRam(r, v), ExistsQuorum2LessRam(r, w)
  PROVE  v = w
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
