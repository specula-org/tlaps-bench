---- MODULE tcp_proof_NetworkType ----
EXTENDS tcp_proof_NetworkTypeScaffold
LEMMA NetworkType ==
  TypeOK <=> /\ tcb \in [Peers -> BOOLEAN]
             /\ connstate \in [Peers -> States]
             /\ network \in [Peers -> Seq(Msgs)]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
