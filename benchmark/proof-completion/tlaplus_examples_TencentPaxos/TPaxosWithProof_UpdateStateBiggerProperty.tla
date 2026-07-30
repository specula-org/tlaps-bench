---- MODULE TPaxosWithProof_UpdateStateBiggerProperty ----
EXTENDS TPaxosWithProof_UpdateStateBiggerPropertyScaffold
LEMMA UpdateStateBiggerProperty ==
     ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in
                [maxBal: Ballot \cup {-1},
                maxVBal: Ballot \cup {-1}, maxVVal: Value \cup {None}],
                UpdateState(q, p, pp), TypeOK
     PROVE  /\ state'[q][q].maxBal \in AllBallot
            /\ state'[q][q].maxBal >= state[q][q].maxBal
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
