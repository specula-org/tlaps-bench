---- MODULE Ben_or83_proofs_DvPSenderWitness ----
EXTENDS Ben_or83_proofs_DvPSenderWitnessScaffold
THEOREM DvPSenderWitness ==
  ASSUME NEW r, NEW v, NEW src \in Senders2(DvPSet(r, v))
  PROVE  \E m \in DvPSet(r, v) : IsD2(m) /\ AsD2(m).src = src
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
