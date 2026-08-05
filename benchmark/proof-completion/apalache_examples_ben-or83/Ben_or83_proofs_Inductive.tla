---- MODULE Ben_or83_proofs_Inductive ----
EXTENDS Ben_or83_proofs_InductiveScaffold
THEOREM Inductive ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  TypeOK' /\ IndInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
