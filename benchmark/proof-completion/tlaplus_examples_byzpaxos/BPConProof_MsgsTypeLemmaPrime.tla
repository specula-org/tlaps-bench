---- MODULE BPConProof_MsgsTypeLemmaPrime ----
EXTENDS BPConProof_MsgsTypeLemmaPrimeScaffold
LEMMA MsgsTypeLemmaPrime ==
        \A m \in msgs' : /\ (m.type = "1a") <=> (m \in msgsOfType("1a")')
                         /\ (m.type = "1b") <=> (m \in 1bmsgs')
                         /\ (m.type = "1c") <=> (m \in 1cmsgs')
                         /\ (m.type = "2a") <=> (m \in 2amsgs')
                         /\ (m.type = "2b") <=> (m \in acceptorMsgsOfType("2b")')
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
