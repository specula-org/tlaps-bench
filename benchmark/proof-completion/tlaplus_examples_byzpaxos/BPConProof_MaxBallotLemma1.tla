---- MODULE BPConProof_MaxBallotLemma1 ----
EXTENDS BPConProof_MaxBallotLemma1Scaffold
LEMMA MaxBallotLemma1 ==
        ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
               IsFiniteSet(S),
               NEW y \in S, \A x \in S : y >= x
        PROVE  y = MaxBallot(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
