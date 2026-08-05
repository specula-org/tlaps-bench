---- MODULE Ben_or83_proofs_Msgs1AddOneRep ----
EXTENDS Ben_or83_proofs_Msgs1AddOneRepScaffold
THEOREM Msgs1AddOneRep ==
  ASSUME NEW A \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW rr0 \in ROUNDS,
         NEW src0 \in ALL,
         NEW val0 \in VALUES,
         NEW f,
         f = [ rr \in ROUNDS |-> { m \in A : m.r = rr } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union { M1(src0, rr0, val0) } ]
         = [ rr \in ROUNDS |->
              { m \in A \union { M1(src0, rr0, val0) } : m.r = rr } ]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
