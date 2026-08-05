---- MODULE Ben_or83_proofs_ShapeSrcFromExists ----
EXTENDS Ben_or83_proofs_ShapeSrcFromExistsScaffold
THEOREM ShapeSrcFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).src \in ALL
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
