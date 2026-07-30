---- MODULE MajorityProof_PositionsFinite ----
EXTENDS MajorityProof_PositionsFiniteScaffold
LEMMA PositionsFinite == 
  ASSUME NEW v, NEW j \in Int
  PROVE  IsFiniteSet(PositionsBefore(v,j))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
