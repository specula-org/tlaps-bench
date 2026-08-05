---- MODULE Ben_or83_proofs_Msgs2Decomp ----
EXTENDS Ben_or83_proofs_Msgs2DecompScaffold
THEOREM Msgs2Decomp ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2[rr] = DPof(A1D, rr) \union QPof(A1Q, rr)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
