---- MODULE Ben_or83_proofs_EarlyMajorityM1HasCorrect ----
EXTENDS Ben_or83_proofs_EarlyMajorityM1HasCorrectScaffold
THEOREM EarlyMajorityM1HasCorrect ==
  ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
         2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
  PROVE  \E id \in CORRECT : \E m \in msgs1[r] : m.src = id /\ m.v = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
