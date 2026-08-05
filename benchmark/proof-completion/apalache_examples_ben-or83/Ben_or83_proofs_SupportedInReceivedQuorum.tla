---- MODULE Ben_or83_proofs_SupportedInReceivedQuorum ----
EXTENDS Ben_or83_proofs_SupportedInReceivedQuorumScaffold
THEOREM SupportedInReceivedQuorum ==
  ASSUME NEW r \in ROUNDS, NEW v \in SupportedValues(r),
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T
  PROVE  Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) >= T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
