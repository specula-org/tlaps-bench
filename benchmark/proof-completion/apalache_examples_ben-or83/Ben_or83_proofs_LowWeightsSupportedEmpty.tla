---- MODULE Ben_or83_proofs_LowWeightsSupportedEmpty ----
EXTENDS Ben_or83_proofs_LowWeightsSupportedEmptyScaffold
THEOREM LowWeightsSupportedEmpty ==
  ASSUME NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T,
         \A v \in VALUES :
           Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) < T + 1
  PROVE  SupportedValues(r) = {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
