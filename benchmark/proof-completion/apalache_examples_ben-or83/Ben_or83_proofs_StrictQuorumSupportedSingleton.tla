---- MODULE Ben_or83_proofs_StrictQuorumSupportedSingleton ----
EXTENDS Ben_or83_proofs_StrictQuorumSupportedSingletonScaffold
THEOREM StrictQuorumSupportedSingleton ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v),
         Cardinality(Senders2(msgs2[r])) >= N - T
  PROVE  v \in SupportedValues(r)
         /\ \A u \in SupportedValues(r) : u = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
