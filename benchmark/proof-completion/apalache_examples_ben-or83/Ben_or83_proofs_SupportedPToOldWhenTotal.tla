---- MODULE Ben_or83_proofs_SupportedPToOldWhenTotal ----
EXTENDS Ben_or83_proofs_SupportedPToOldWhenTotalScaffold
THEOREM SupportedPToOldWhenTotal ==
  ASSUME TypeOK,
         NEW r \in ROUNDS,
         NEW v \in SupportedValuesP(r),
         Cardinality(Senders2(msgs2[r])) >= N - T,
         msgs2[r] \subseteq msgs2'[r]
  PROVE  v \in SupportedValues(r)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
