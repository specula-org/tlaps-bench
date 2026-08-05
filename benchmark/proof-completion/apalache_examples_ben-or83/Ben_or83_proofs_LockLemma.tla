---- MODULE Ben_or83_proofs_LockLemma ----
EXTENDS Ben_or83_proofs_LockLemmaScaffold
THEOREM LockLemma ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T
  PROVE  \A r \in ROUNDS :
            r >= a =>
              (\A w \in VALUES :
                 /\ ExistsQuorum2LessRam(r, w)
                 /\ Cardinality(Senders2(msgs2[r])) >= N - T
                 => w = v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
