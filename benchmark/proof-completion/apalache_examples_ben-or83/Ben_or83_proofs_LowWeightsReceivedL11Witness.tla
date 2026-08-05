---- MODULE Ben_or83_proofs_LowWeightsReceivedL11Witness ----
EXTENDS Ben_or83_proofs_LowWeightsReceivedL11WitnessScaffold
THEOREM LowWeightsReceivedL11Witness ==
  ASSUME TypeOK,
         NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T,
         \A v \in VALUES :
           Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) < T + 1
  PROVE  LET n0 == Cardinality(DvSet(r, 0))
             n1 == Cardinality(DvSet(r, 1))
             nq == Cardinality(QSet(r))
         IN
         \E x0, x1 \in 0..N:
           /\ x0 <= n0 /\ x1 <= n1
           /\ x0 + x1 + nq >= N - T
           /\ 2 * x0 <= N + T
           /\ 2 * x1 <= N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
