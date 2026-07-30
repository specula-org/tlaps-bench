---- MODULE PaxosCommit_proof_MajorityNonEmpty ----
EXTENDS PaxosCommit_proof_MajorityNonEmptyScaffold
LEMMA MajorityNonEmpty == \A MS \in Majority : MS # {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
