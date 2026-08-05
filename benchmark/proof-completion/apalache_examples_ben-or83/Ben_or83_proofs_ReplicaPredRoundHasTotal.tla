---- MODULE Ben_or83_proofs_ReplicaPredRoundHasTotal ----
EXTENDS Ben_or83_proofs_ReplicaPredRoundHasTotalScaffold
THEOREM ReplicaPredRoundHasTotal ==
  ASSUME TypeOK, IndInv,
         NEW id \in CORRECT,
         round[id] > 1,
         NEW r \in ROUNDS,
         r = round[id] - 1
  PROVE  Cardinality(Senders2(msgs2[r])) >= N - T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
