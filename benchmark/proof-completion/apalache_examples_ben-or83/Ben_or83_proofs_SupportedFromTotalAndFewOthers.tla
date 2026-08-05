---- MODULE Ben_or83_proofs_SupportedFromTotalAndFewOthers ----
EXTENDS Ben_or83_proofs_SupportedFromTotalAndFewOthersScaffold
THEOREM SupportedFromTotalAndFewOthers ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(Senders2(msgs2[r])) >= N - T,
         Cardinality(Senders2({ m \in msgs2[r]: IsQ2(m) \/ AsD2(m).v /= v })) < N - 2 * T
  PROVE  v \in SupportedValues(r)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
