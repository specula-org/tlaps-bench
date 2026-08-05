---- MODULE Ben_or83_proofs_StrictQuorumCarriesToQuorumRound ----
EXTENDS Ben_or83_proofs_StrictQuorumCarriesToQuorumRoundScaffold
THEOREM StrictQuorumCarriesToQuorumRound ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         NEW r \in ROUNDS, r >= a,
         NEW w \in VALUES, ExistsQuorum2LessRam(r, w),
         Cardinality(Senders2(msgs2[r])) >= N - T
  PROVE  ExistsQuorum2LessRam(r, v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
