---- MODULE Ben_or83_proofs_FaultyMsgs2AddedFaulty ----
EXTENDS Ben_or83_proofs_FaultyMsgs2AddedFaultyScaffold
THEOREM FaultyMsgs2AddedFaulty ==
  ASSUME NEW rr0 \in ROUNDS,
         NEW F2D \in SUBSET FaultyD2Records(rr0),
         NEW F2Q \in SUBSET FaultyQ2Records(rr0),
         NEW m,
         m \in { D2(mm.src, rr0, mm.v): mm \in F2D }
              \union { Q2(mm.src, rr0): mm \in F2Q }
  PROVE  (IsD2(m) => AsD2(m).src \in FAULTY)
         /\ (IsQ2(m) => AsQ2(m).src \in FAULTY)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
