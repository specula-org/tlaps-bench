---- MODULE Ben_or83_proofs_SupportedValuesPrimeIsP ----
EXTENDS Ben_or83_proofs_SupportedValuesPrimeIsPScaffold
THEOREM SupportedValuesPrimeIsP ==
  ASSUME NEW r \in ROUNDS
  PROVE  SupportedValues(r)' = SupportedValuesP(r)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
