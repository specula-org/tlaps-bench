---- MODULE Ben_or83_proofs_Agreement ----
EXTENDS Ben_or83_proofs_AgreementScaffold
THEOREM Agreement == TypeOK /\ IndInv => AgreementInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
