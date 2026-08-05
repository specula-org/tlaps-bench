---- MODULE Ben_or83_proofs_ReceivedDQuorumDominatesSupported ----
EXTENDS Ben_or83_proofs_ReceivedDQuorumDominatesSupportedScaffold
THEOREM ReceivedDQuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         NEW v \in VALUES,
         Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) >= T + 1,
         NEW w \in SupportedValues(r)
  PROVE  w = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
