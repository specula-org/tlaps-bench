---- MODULE Ben_or83_proofs_Msgs2AddQRep ----
EXTENDS Ben_or83_proofs_Msgs2AddQRepScaffold
THEOREM Msgs2AddQRep ==
  ASSUME NEW AD \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW AQ \in SUBSET [ src: ALL, r: ROUNDS ],
         NEW rr0 \in ROUNDS,
         NEW src0 \in ALL,
         NEW f,
         f = [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union { Q2(src0, rr0) } ]
         = [ rr \in ROUNDS |->
             { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
               \union { Q2(mm.src, rr):
                 mm \in { m \in AQ \union { [ src |-> src0, r |-> rr0 ] }:
                   m.r = rr } } ]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
