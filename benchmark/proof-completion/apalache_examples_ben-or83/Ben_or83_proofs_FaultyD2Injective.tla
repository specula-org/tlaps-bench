---- MODULE Ben_or83_proofs_FaultyD2Injective ----
EXTENDS Ben_or83_proofs_FaultyD2InjectiveScaffold
THEOREM FaultyD2Injective ==
  ASSUME NEW r, NEW v,
         \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in FaultyD2(r, v), NEW b \in FaultyD2(r, v),
         FaultyD2Fn(r, v)[a] = FaultyD2Fn(r, v)[b]
  PROVE  a = b
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
