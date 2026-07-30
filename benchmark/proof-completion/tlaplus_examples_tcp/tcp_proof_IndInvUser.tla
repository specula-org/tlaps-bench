---- MODULE tcp_proof_IndInvUser ----
EXTENDS tcp_proof_IndInvUserScaffold
LEMMA IndInvUser ==
  ASSUME IndInv, TypeOK',
         NEW local \in Peers, NEW remote \in Peers,
         \/ PASSIVE_OPEN(local, remote)
         \/ ACTIVE_OPEN(local, remote)
         \/ CLOSE_SYN_SENT(local, remote)
         \/ CLOSE_SYN_RECEIVED(local, remote)
         \/ CLOSE_LISTEN(local, remote)
         \/ CLOSE_ESTABLISHED(local, remote)
         \/ CLOSE_CLOSE_WAIT(local, remote)
         \/ SEND(local, remote)
  PROVE  IndInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
