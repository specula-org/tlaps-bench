---- MODULE PaxosProof_WFmsgs ----
EXTENDS PaxosProof_WFmsgsScaffold
THEOREM WFmsgs == TypeOK => WellFormedMessages
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
