---- MODULE Ben_or83_proofs_LockedReceiveStrictD ----
EXTENDS Ben_or83_proofs_LockedReceiveStrictDScaffold
THEOREM LockedReceiveStrictD ==
  ASSUME TypeOK, IndInv,
         NEW id0 \in CORRECT,
         Step3(id0),
         decision[id0] # NO_DECISION,
         NEW received \in SUBSET msgs2[round[id0]],
         Cardinality(Senders2(received)) = N - T
  PROVE  2 * Cardinality(Senders2({ m \in received:
                                      IsD2(m) /\ AsD2(m).v = decision[id0] }))
            > N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
