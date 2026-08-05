---- MODULE Ben_or83_proofs_Msgs2Step2Mono ----
EXTENDS Ben_or83_proofs_Msgs2Step2MonoScaffold
THEOREM Msgs2Step2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(msgs2'[r])
          /\ Cardinality(msgs2[r]) <= Cardinality(msgs2'[r])
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
