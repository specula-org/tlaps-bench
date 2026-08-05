---- MODULE Ben_or83_proofs_ShapeHelper ----
EXTENDS Ben_or83_proofs_ShapeHelperScaffold
THEOREM ShapeHelper ==
  ASSUME NEW rr, NEW A1D, NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).r = rr
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
