---- MODULE Ben_or83_proofs_StrictQuorumNextReceiveStrictD ----
EXTENDS Ben_or83_proofs_StrictQuorumNextReceiveStrictDScaffold
THEOREM StrictQuorumNextReceiveStrictD ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         NEW received \in SUBSET msgs2[a + 1],
         Cardinality(Senders2(received)) = N - T
  PROVE  2 * Cardinality(Senders2({ m \in received:
                                      IsD2(m) /\ AsD2(m).v = v }))
            > N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
