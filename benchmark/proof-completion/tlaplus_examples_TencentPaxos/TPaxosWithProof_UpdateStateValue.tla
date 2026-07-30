---- MODULE TPaxosWithProof_UpdateStateValue ----
EXTENDS TPaxosWithProof_UpdateStateValueScaffold
LEMMA UpdateStateValue ==
          ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in State, pp.maxBal >= pp.maxVBal,
                     UpdateState(q, p, pp), Inv
            PROVE \/ /\ state'[q][q].maxVBal = state[q][q].maxVBal
                     /\ state'[q][q].maxVVal = state[q][q].maxVVal
                  \/ /\ state'[q][q].maxVBal = pp.maxVBal
                     /\ pp.maxVBal = pp.maxBal
                     /\ state'[q][q].maxVVal = pp.maxVVal
                     /\ state'[q][q].maxBal = pp.maxVBal
               /\ state'[q][q].maxBal >= state'[q][q].maxVBal
               /\ state'[q][q].maxVBal >= state[q][q].maxVBal
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
