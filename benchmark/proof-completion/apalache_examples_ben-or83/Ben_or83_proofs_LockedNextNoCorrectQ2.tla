---- MODULE Ben_or83_proofs_LockedNextNoCorrectQ2 ----
EXTENDS Ben_or83_proofs_LockedNextNoCorrectQ2Scaffold
THEOREM LockedNextNoCorrectQ2 ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         NEW m \in msgs2[a + 1],
         IsQ2(m),
         AsQ2(m).src \in CORRECT
  PROVE  FALSE
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
