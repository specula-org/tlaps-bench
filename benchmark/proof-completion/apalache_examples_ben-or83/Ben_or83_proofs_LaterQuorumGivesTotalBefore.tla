---- MODULE Ben_or83_proofs_LaterQuorumGivesTotalBefore ----
EXTENDS Ben_or83_proofs_LaterQuorumGivesTotalBeforeScaffold
THEOREM LaterQuorumGivesTotalBefore ==
  ASSUME TypeOK, IndInv,
         NEW b \in ROUNDS, NEW r \in ROUNDS, b < r,
         NEW w \in VALUES, ExistsQuorum2LessRam(r, w)
  PROVE  Cardinality(Senders2(msgs2[b])) >= N - T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
