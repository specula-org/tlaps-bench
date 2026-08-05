---- MODULE Ben_or83_proofs_LockedFullCorrectType2Strict ----
EXTENDS Ben_or83_proofs_LockedFullCorrectType2StrictScaffold
THEOREM LockedFullCorrectType2Strict ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(Senders2(msgs2[r])) >= N - T,
         \A m \in msgs2[r] :
           ((IsD2(m) => AsD2(m).src \in CORRECT)
             /\ (IsQ2(m) => AsQ2(m).src \in CORRECT))
              => IsD2(m) /\ AsD2(m).v = v
  PROVE  ExistsQuorum2LessRam(r, v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
