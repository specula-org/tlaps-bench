---- MODULE Ben_or83_proofs_DvInjective ----
EXTENDS Ben_or83_proofs_DvInjectiveScaffold
THEOREM DvInjective ==
  ASSUME NEW r, NEW v, \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in DvSet(r, v), NEW b \in DvSet(r, v), DvFn(r, v)[a] = DvFn(r, v)[b]
  PROVE  a = b
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
