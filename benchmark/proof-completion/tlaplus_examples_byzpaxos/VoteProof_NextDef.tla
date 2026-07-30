---- MODULE VoteProof_NextDef ----
EXTENDS VoteProof_NextDefScaffold
LEMMA NextDef ==
  TypeOK => 
   (Next =  \E self \in Acceptor :
                 \E b \in Ballot : BallotAction(self, b) )
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
