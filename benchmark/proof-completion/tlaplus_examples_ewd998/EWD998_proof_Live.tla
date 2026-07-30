---- MODULE EWD998_proof_Live ----
EXTENDS EWD998_proof_LiveScaffold
USE NAssumption
THEOREM Live == []TypeOK /\ []Inv /\ [][Next]_vars /\ WF_vars(System) => Liveness
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
