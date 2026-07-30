---- MODULE BPConProof_MaxBallotLemma2 ----
EXTENDS BPConProof_MaxBallotLemma2Scaffold
LEMMA MaxBallotLemma2 ==
  ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
         NEW T \in SUBSET (Ballot \cup {-1}),
         IsFiniteSet(S), IsFiniteSet(T)
  PROVE  MaxBallot(S \cup T) = IF MaxBallot(S) >= MaxBallot(T)
                               THEN MaxBallot(S) ELSE MaxBallot(T)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
