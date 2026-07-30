---- MODULE tcp_proof_InvIsAB ----
EXTENDS tcp_proof_InvIsABScaffold
LEMMA InvIsAB ==
  Inv <=> ((network[A] = <<>> /\ network[B] = <<>>)
              => (connstate[A] = "ESTABLISHED" <=> connstate[B] = "ESTABLISHED"))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
