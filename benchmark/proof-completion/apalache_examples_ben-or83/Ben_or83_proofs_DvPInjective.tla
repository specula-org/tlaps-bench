---- MODULE Ben_or83_proofs_DvPInjective ----
EXTENDS Ben_or83_proofs_DvPInjectiveScaffold
THEOREM DvPInjective ==
  ASSUME NEW r, NEW v, \A m \in msgs2'[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in DvPSet(r, v), NEW b \in DvPSet(r, v), DvPFn(r, v)[a] = DvPFn(r, v)[b]
  PROVE  a = b
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
