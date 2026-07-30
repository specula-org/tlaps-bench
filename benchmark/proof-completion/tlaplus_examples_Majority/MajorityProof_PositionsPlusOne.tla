---- MODULE MajorityProof_PositionsPlusOne ----
EXTENDS MajorityProof_PositionsPlusOneScaffold
LEMMA PositionsPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  PositionsBefore(v, j+1) =
         IF seq[j] = v THEN PositionsBefore(v,j) \union {j}
         ELSE PositionsBefore(v,j)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
