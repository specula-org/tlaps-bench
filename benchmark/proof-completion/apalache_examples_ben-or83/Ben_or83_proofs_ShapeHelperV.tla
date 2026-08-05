---- MODULE Ben_or83_proofs_ShapeHelperV ----
EXTENDS Ben_or83_proofs_ShapeHelperVScaffold
THEOREM ShapeHelperV ==
  ASSUME NEW rr, NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ], NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).v \in VALUES
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
