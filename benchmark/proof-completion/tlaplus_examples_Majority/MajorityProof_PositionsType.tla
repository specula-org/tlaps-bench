---- MODULE MajorityProof_PositionsType ----
EXTENDS MajorityProof_PositionsTypeScaffold
LEMMA PositionsType == \A v, j : PositionsBefore(v,j) \in SUBSET (1 .. j-1)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
