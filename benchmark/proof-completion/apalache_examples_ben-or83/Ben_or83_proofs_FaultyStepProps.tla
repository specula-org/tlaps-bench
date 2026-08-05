---- MODULE Ben_or83_proofs_FaultyStepProps ----
EXTENDS Ben_or83_proofs_FaultyStepPropsScaffold
THEOREM FaultyStepProps ==
  ASSUME TypeOK, FaultyStep
  PROVE  /\ value' = value /\ decision' = decision /\ round' = round /\ step' = step
         /\ \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr] /\ msgs2[rr] \subseteq msgs2'[rr]
         /\ \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
         /\ \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
