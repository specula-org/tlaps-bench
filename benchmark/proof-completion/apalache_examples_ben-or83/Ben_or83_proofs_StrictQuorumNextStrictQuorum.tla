---- MODULE Ben_or83_proofs_StrictQuorumNextStrictQuorum ----
EXTENDS Ben_or83_proofs_StrictQuorumNextStrictQuorumScaffold
THEOREM StrictQuorumNextStrictQuorum ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         Cardinality(Senders2(msgs2[a + 1])) >= N - T
  PROVE  ExistsQuorum2LessRam(a + 1, v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
