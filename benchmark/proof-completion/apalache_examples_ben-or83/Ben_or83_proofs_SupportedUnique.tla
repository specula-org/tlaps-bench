---- MODULE Ben_or83_proofs_SupportedUnique ----
EXTENDS Ben_or83_proofs_SupportedUniqueScaffold
THEOREM SupportedUnique ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in SupportedValues(r), NEW w \in SupportedValues(r)
  PROVE  v = w
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
