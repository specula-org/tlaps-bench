---- MODULE Ben_or83_proofs_ShapeFromExists ----
EXTENDS Ben_or83_proofs_ShapeFromExistsScaffold
THEOREM ShapeFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).r = rr
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
