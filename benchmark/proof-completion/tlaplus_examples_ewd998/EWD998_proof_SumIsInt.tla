---- MODULE EWD998_proof_SumIsInt ----
EXTENDS EWD998_proof_SumIsIntScaffold
USE NAssumption
LEMMA SumIsInt == 
  ASSUME NEW fun \in [Node -> Int],
         NEW inds \in SUBSET Node
  PROVE  Sum(fun, inds) \in Int
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
