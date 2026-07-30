---- MODULE TPaxosWithProof_UpdateStateTypeOKProperty ----
EXTENDS TPaxosWithProof_UpdateStateTypeOKPropertyScaffold
LEMMA UpdateStateTypeOKProperty ==
     ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in State,
                UpdateState(q, p, pp), TypeOK
     PROVE state' \in [Participant -> [Participant -> State]]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
