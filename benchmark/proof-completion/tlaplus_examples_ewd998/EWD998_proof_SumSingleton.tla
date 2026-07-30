---- MODULE EWD998_proof_SumSingleton ----
EXTENDS EWD998_proof_SumSingletonScaffold
USE NAssumption
LEMMA SumSingleton ==
  ASSUME NEW fun \in [Node -> Int], NEW x \in Node
  PROVE  Sum(fun, {x}) = fun[x]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
