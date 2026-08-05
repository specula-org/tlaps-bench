---- MODULE Ben_or83_proofs_SupportedValuesPFrame ----
EXTENDS Ben_or83_proofs_SupportedValuesPFrameScaffold
THEOREM SupportedValuesPFrame ==
  ASSUME NEW r \in ROUNDS, msgs2' = msgs2
  PROVE  SupportedValuesP(r) = SupportedValues(r)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
