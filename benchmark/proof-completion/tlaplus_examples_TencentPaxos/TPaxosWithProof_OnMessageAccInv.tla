---- MODULE TPaxosWithProof_OnMessageAccInv ----
EXTENDS TPaxosWithProof_OnMessageAccInvScaffold
LEMMA OnMessageAccInv ==
    ASSUME NEW qq \in Participant, OnMessage(qq), Inv, TypeOK'
     PROVE AccInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
