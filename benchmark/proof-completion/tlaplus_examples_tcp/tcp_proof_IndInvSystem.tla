---- MODULE tcp_proof_IndInvSystem ----
EXTENDS tcp_proof_IndInvSystemScaffold
LEMMA IndInvSystem ==
  ASSUME IndInv, TypeOK',
         NEW local \in Peers, NEW remote \in Peers,
         \/ SynSent(local, remote)
         \/ SynReceived(local, remote)
         \/ Listen(local, remote)
         \/ Established(local, remote)
         \/ FinWait1(local, remote)
         \/ FinWait2(local, remote)
         \/ Closing(local, remote)
         \/ LastAck(local, remote)
         \/ TimeWait(local, remote)
         \/ Note2(local, remote)
  PROVE  IndInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
