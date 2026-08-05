---- MODULE Ben_or83_proofs_QuorumHasM1Majority ----
EXTENDS Ben_or83_proofs_QuorumHasM1MajorityScaffold
THEOREM QuorumHasM1Majority ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v)
  PROVE  LET Sv == { m \in msgs1[r] : m.v = v } IN
           2 * Cardinality(Senders1(Sv)) > N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
