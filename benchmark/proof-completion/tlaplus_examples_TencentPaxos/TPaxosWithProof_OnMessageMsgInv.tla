---- MODULE TPaxosWithProof_OnMessageMsgInv ----
EXTENDS TPaxosWithProof_OnMessageMsgInvScaffold
LEMMA OnMessageMsgInv == ASSUME NEW q \in Participant, OnMessage(q), Inv, TypeOK'
                          PROVE MsgInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
