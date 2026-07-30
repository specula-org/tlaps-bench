---- MODULE tcp_proof_IndInvReset ----
EXTENDS tcp_proof_IndInvResetScaffold
LEMMA IndInvReset ==
  ASSUME IndInv, TypeOK',
         NEW local \in Peers, NEW remote \in Peers,
         Note3(local, remote)
  PROVE  IndInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
