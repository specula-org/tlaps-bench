---- MODULE Ben_or83_proofs_TypePres ----
EXTENDS Ben_or83_proofs_TypePresScaffold
THEOREM TypePres ==
  ASSUME TypeOK, [Next]_vars
  PROVE  TypeOK'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
