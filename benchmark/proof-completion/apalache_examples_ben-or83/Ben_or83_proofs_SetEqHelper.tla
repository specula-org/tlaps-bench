---- MODULE Ben_or83_proofs_SetEqHelper ----
EXTENDS Ben_or83_proofs_SetEqHelperScaffold
THEOREM SetEqHelper ==
  ASSUME NEW rr, NEW A1D, NEW A1Q
  PROVE  { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
            \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } }
         = DPof(A1D, rr) \union QPof(A1Q, rr)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
