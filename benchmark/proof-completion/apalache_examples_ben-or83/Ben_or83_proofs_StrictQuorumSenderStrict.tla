---- MODULE Ben_or83_proofs_StrictQuorumSenderStrict ----
EXTENDS Ben_or83_proofs_StrictQuorumSenderStrictScaffold
THEOREM StrictQuorumSenderStrict ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v)
  PROVE  /\ Cardinality(Senders2(DvSet(r, v))) >= T + 1
          /\ 2 * Cardinality(Senders2(DvSet(r, v))) > N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
