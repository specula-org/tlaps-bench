---- MODULE Ben_or83_proofs_QuorumHasCorrectM1 ----
EXTENDS Ben_or83_proofs_QuorumHasCorrectM1Scaffold
THEOREM QuorumHasCorrectM1 ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v)
  PROVE  \E id \in CORRECT : \E m \in msgs1[r] : m.src = id /\ m.v = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
