---- MODULE Ben_or83_proofs_QPInjective ----
EXTENDS Ben_or83_proofs_QPInjectiveScaffold
THEOREM QPInjective ==
  ASSUME NEW r, \A m \in msgs2'[r] : IsQ2(m) => AsQ2(m).r = r,
         NEW a \in QPSet(r), NEW b \in QPSet(r), QPFn(r)[a] = QPFn(r)[b]
  PROVE  a = b
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
