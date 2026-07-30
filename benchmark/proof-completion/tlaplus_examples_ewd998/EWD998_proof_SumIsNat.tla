---- MODULE EWD998_proof_SumIsNat ----
EXTENDS EWD998_proof_SumIsNatScaffold
USE NAssumption
LEMMA SumIsNat == 
  ASSUME NEW fun \in [Node -> Nat],
         NEW inds \in SUBSET Node
  PROVE  Sum(fun, inds) \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
