---- MODULE Ben_or83_proofs_ShapeHelperR ----
EXTENDS Ben_or83_proofs_ShapeHelperRScaffold
THEOREM ShapeHelperR ==
  ASSUME NEW rr, NEW A1D, NEW A1Q, NEW m, m \in DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
