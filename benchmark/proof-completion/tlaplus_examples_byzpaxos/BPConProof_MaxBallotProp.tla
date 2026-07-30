---- MODULE BPConProof_MaxBallotProp ----
EXTENDS BPConProof_MaxBallotPropScaffold
THEOREM MaxBallotProp  ==
  ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
         IsFiniteSet(S)
  PROVE  IF S = {} THEN MaxBallot(S) = -1
                   ELSE /\ MaxBallot(S) \in S
                        /\ \A x \in S : MaxBallot(S) >= x
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
