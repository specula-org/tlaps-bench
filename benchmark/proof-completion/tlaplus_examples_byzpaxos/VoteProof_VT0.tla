---- MODULE VoteProof_VT0 ----
EXTENDS VoteProof_VT0Scaffold
LEMMA VT0 == /\ TypeOK
             /\ VInv1
             /\ VInv2
             => \A v, w \in Value, b, c \in Ballot : 
                   (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
