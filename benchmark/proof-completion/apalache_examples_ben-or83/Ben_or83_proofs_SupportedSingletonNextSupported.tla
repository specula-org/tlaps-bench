---- MODULE Ben_or83_proofs_SupportedSingletonNextSupported ----
EXTENDS Ben_or83_proofs_SupportedSingletonNextSupportedScaffold
THEOREM SupportedSingletonNextSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW w \in SupportedValues(r + 1)
  PROVE  w = v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
