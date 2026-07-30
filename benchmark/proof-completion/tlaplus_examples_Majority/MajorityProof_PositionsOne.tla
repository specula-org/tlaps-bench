---- MODULE MajorityProof_PositionsOne ----
EXTENDS MajorityProof_PositionsOneScaffold
LEMMA PositionsOne == \A v : PositionsBefore(v,1) = {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
