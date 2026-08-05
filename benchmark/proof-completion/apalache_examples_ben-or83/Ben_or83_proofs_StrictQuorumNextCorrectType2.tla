---- MODULE Ben_or83_proofs_StrictQuorumNextCorrectType2 ----
EXTENDS Ben_or83_proofs_StrictQuorumNextCorrectType2Scaffold
THEOREM StrictQuorumNextCorrectType2 ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         NEW m \in msgs2[a + 1],
         (IsD2(m) => AsD2(m).src \in CORRECT)
           /\ (IsQ2(m) => AsQ2(m).src \in CORRECT)
  PROVE  IsD2(m) /\ AsD2(m).v = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
