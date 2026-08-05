---- MODULE Ben_or83_proofs_DvStep2Mono ----
EXTENDS Ben_or83_proofs_DvStep2MonoScaffold
THEOREM DvStep2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  /\ IsFiniteSet({ m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v })
          /\ Cardinality(DvSet(r, v))
             <= Cardinality({ m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v })
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
