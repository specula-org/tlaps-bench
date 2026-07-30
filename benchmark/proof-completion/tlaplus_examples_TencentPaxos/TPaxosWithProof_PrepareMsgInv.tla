---- MODULE TPaxosWithProof_PrepareMsgInv ----
EXTENDS TPaxosWithProof_PrepareMsgInvScaffold
LEMMA PrepareMsgInv == ASSUME NEW p \in Participant, NEW b \in Ballot, Prepare(p, b), Inv, TypeOK'
                        PROVE MsgInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
