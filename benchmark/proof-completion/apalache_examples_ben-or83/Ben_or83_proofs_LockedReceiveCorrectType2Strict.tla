---- MODULE Ben_or83_proofs_LockedReceiveCorrectType2Strict ----
EXTENDS Ben_or83_proofs_LockedReceiveCorrectType2StrictScaffold
THEOREM LockedReceiveCorrectType2Strict ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T,
         \A m \in received :
           ((IsD2(m) => AsD2(m).src \in CORRECT)
             /\ (IsQ2(m) => AsQ2(m).src \in CORRECT))
              => IsD2(m) /\ AsD2(m).v = v
  PROVE  2 * Cardinality(Senders2({ m \in received:
                                      IsD2(m) /\ AsD2(m).v = v }))
            > N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
