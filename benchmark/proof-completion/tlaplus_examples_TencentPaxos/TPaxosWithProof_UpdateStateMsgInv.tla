---- MODULE TPaxosWithProof_UpdateStateMsgInv ----
EXTENDS TPaxosWithProof_UpdateStateMsgInvScaffold
LEMMA UpdateStateMsgInv ==
    ASSUME NEW q \in Participant, NEW p \in Participant, NEW mm \in msgs, mm.from = p, Inv, q \in mm.to, Next,
           UpdateState(q, p, mm.state[p]), TypeOK', Send([from |-> q, to |-> {mm.from}, state |-> state'[q]])
     PROVE MsgInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
