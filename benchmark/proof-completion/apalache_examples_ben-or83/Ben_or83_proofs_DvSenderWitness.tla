---- MODULE Ben_or83_proofs_DvSenderWitness ----
EXTENDS Ben_or83_proofs_DvSenderWitnessScaffold
THEOREM DvSenderWitness ==
  ASSUME NEW r, NEW v, NEW id \in Senders2(DvSet(r, v))
  PROVE  \E md \in DvSet(r, v) : IsD2(md) /\ AsD2(md).src = id
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
