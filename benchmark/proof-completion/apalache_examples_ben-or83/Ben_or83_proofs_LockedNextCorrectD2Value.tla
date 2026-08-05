---- MODULE Ben_or83_proofs_LockedNextCorrectD2Value ----
EXTENDS Ben_or83_proofs_LockedNextCorrectD2ValueScaffold
THEOREM LockedNextCorrectD2Value ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         NEW m \in msgs2[a + 1],
         IsD2(m),
         AsD2(m).src \in CORRECT
  PROVE  AsD2(m).v = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
