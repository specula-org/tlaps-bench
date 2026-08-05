---- MODULE Ben_or83_proofs_SupportedSingletonNextQuorum ----
EXTENDS Ben_or83_proofs_SupportedSingletonNextQuorumScaffold
THEOREM SupportedSingletonNextQuorum ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW w \in VALUES, ExistsQuorum2LessRam(r + 1, w)
  PROVE  w = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
