---- MODULE PaxosCommit_proof_MaximumIsMaxFn ----
EXTENDS PaxosCommit_proof_MaximumIsMaxFnScaffold
LEMMA MaximumIsMaxFn ==
  ASSUME NEW S
  PROVE  Maximum(S) = MaxFn(S)[S]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
