---- MODULE Ben_or83_proofs_QInjective ----
EXTENDS Ben_or83_proofs_QInjectiveScaffold
THEOREM QInjective ==
  ASSUME NEW r, \A m \in msgs2[r] : IsQ2(m) => AsQ2(m).r = r,
         NEW a \in QSet(r), NEW b \in QSet(r), QFn(r)[a] = QFn(r)[b]
  PROVE  a = b
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
