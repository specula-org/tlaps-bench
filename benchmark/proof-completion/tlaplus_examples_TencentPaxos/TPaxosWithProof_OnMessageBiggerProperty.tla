---- MODULE TPaxosWithProof_OnMessageBiggerProperty ----
EXTENDS TPaxosWithProof_OnMessageBiggerPropertyScaffold
LEMMA OnMessageBiggerProperty ==
     ASSUME NEW q \in Participant, OnMessage(q), TypeOK
     PROVE  state'[q][q].maxBal >= state[q][q].maxBal
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
