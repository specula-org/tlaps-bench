---- MODULE EWD998_proof_SumZero ----
EXTENDS EWD998_proof_SumZeroScaffold
USE NAssumption
LEMMA SumZero ==
  ASSUME NEW fun \in [Node -> Int], NEW inds \in SUBSET Node,
         \A i \in inds : fun[i] = 0
  PROVE  Sum(fun, inds) = 0
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
