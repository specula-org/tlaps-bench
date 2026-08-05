---- MODULE Ben_or83_proofs_ShapeSrcQFromExists ----
EXTENDS Ben_or83_proofs_ShapeSrcQFromExistsScaffold
THEOREM ShapeSrcQFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsQ2(m) => AsQ2(m).src \in ALL
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
