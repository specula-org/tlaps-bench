---- MODULE EWD998_proof_SumEmpty ----
EXTENDS EWD998_proof_SumEmptyScaffold
USE NAssumption
LEMMA SumEmpty ==
  ASSUME NEW fun
  PROVE  Sum(fun, {}) = 0
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
