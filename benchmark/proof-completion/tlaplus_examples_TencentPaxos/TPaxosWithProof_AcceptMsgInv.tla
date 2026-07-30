---- MODULE TPaxosWithProof_AcceptMsgInv ----
EXTENDS TPaxosWithProof_AcceptMsgInvScaffold
LEMMA AcceptMsgInv == ASSUME NEW p \in Participant, NEW b \in Ballot, NEW v \in Value, Accept(p, b, v), Inv, TypeOK'
                       PROVE MsgInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
