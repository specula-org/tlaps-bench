---- MODULE VoteProof_VT0Prime ----
EXTENDS VoteProof_VT0PrimeScaffold
LEMMA VT0Prime == 
  /\ TypeOK'
  /\ VInv1'
  /\ VInv2'
  => \A v, w \in Value, b, c \in Ballot : 
        (b > c) /\ SafeAt(b, v)' /\ ChosenIn(c, w)' => (v = w)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
