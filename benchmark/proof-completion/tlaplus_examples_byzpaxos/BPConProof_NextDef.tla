---- MODULE BPConProof_NextDef ----
EXTENDS BPConProof_NextDefScaffold
LEMMA NextDef ==
 Next <=> \/ \E self \in Acceptor :
                \E b \in Ballot : \/ Phase1b(self, b)
                                  \/ Phase2av(self, b)
                                  \/ Phase2b(self,b)
                                  \/ LearnsSent(self, b)
          \/ \E self \in Ballot : \/ Phase1a(self)
                                  \/ Phase1c(self)
          \/ \E self \in FakeAcceptor : FakingAcceptor(self)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
