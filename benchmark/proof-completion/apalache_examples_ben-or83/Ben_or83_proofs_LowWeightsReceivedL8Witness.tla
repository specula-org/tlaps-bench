---- MODULE Ben_or83_proofs_LowWeightsReceivedL8Witness ----
EXTENDS Ben_or83_proofs_LowWeightsReceivedL8WitnessScaffold
THEOREM LowWeightsReceivedL8Witness ==
  ASSUME TypeOK,
         NEW r \in ROUNDS,
         NEW received \in SUBSET msgs1[r],
         Cardinality(Senders1(received)) >= N - T,
         \A vv \in VALUES :
           2 * Cardinality(Senders1({ m \in received : m.v = vv })) <= N + T
  PROVE  LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] })
             n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] })
             nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } })
         IN
         \E x0, x1 \in 0..N :
           /\ x0 <= n0 /\ x1 <= n1
           /\ x0 + x1 + nf >= N - T
           /\ 2 * x0 <= N + T
           /\ 2 * x1 <= N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
