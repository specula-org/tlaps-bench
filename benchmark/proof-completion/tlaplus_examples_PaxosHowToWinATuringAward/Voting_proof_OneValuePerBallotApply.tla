---- MODULE Voting_proof_OneValuePerBallotApply ----
EXTENDS Voting_proof_OneValuePerBallotApplyScaffold
LEMMA OneValuePerBallotApply ==
  ASSUME OneValuePerBallot,
         NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW bb \in Ballot,
         NEW v1 \in Value, NEW v2 \in Value,
         VotedFor(a1, bb, v1), VotedFor(a2, bb, v2)
  PROVE  v1 = v2
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
