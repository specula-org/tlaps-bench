---- MODULE Ben_or83_proofs_StrictQuorumFewOthers ----
EXTENDS Ben_or83_proofs_StrictQuorumFewOthersScaffold
THEOREM StrictQuorumFewOthers ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v)
  PROVE  Cardinality(Senders2({ m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v }))
            < N - 2 * T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
