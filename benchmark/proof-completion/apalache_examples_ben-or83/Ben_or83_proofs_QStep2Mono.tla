---- MODULE Ben_or83_proofs_QStep2Mono ----
EXTENDS Ben_or83_proofs_QStep2MonoScaffold
THEOREM QStep2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet({ m \in msgs2'[r] : IsQ2(m) })
          /\ Cardinality(QSet(r))
             <= Cardinality({ m \in msgs2'[r] : IsQ2(m) })
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
