---- MODULE TPaxosWithProof_UpdateStateViewValue ----
EXTENDS TPaxosWithProof_UpdateStateViewValueScaffold
LEMMA UpdateStateViewValue ==
         ASSUME NEW q \in Participant, NEW p \in Participant, NEW m \in msgs, p = m.from, q \in m.to,
                    UpdateState(q, p, m.state[m.from]), Inv, TypeOK'
         PROVE /\ state'[q][p].maxBal >= state'[q][p].maxVBal
               /\ \/ /\ state'[q][p].maxBal = state[q][p].maxBal
                     /\ state'[q][p].maxVBal = state[q][p].maxVBal
                     /\ state'[q][p].maxVVal = state[q][p].maxVVal
                  \/ /\ state'[q][p].maxBal = m.state[m.from].maxBal
                     /\ state'[q][p].maxVBal = m.state[m.from].maxVBal
                     /\ state'[q][p].maxVVal = m.state[m.from].maxVVal
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
