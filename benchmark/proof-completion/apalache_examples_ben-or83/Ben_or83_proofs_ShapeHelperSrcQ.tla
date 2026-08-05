---- MODULE Ben_or83_proofs_ShapeHelperSrcQ ----
EXTENDS Ben_or83_proofs_ShapeHelperSrcQScaffold
THEOREM ShapeHelperSrcQ ==
  ASSUME NEW rr, NEW A1D, NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ], NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsQ2(m)
  PROVE  AsQ2(m).src \in ALL
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
