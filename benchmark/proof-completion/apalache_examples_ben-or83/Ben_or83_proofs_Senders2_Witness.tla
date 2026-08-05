---- MODULE Ben_or83_proofs_Senders2_Witness ----
EXTENDS Ben_or83_proofs_Senders2_WitnessScaffold
THEOREM Senders2_Witness ==
  ASSUME NEW S, NEW id \in Senders2(S)
  PROVE  \E m \in S :
           (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
