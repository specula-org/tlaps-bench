---- MODULE Ben_or83_proofs_TypeOKPrimeIntro ----
EXTENDS Ben_or83_proofs_TypeOKPrimeIntroScaffold
THEOREM TypeOKPrimeIntro ==
  ASSUME value' \in [ CORRECT -> VALUES ],
         decision' \in [ CORRECT -> VALUES \union { NO_DECISION } ],
         round' \in [ CORRECT -> ROUNDS ],
         step' \in [ CORRECT -> { S1, S2, S3 } ],
         \E A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
           msgs1' = [ r \in ROUNDS |-> { m \in A1 : m.r = r } ],
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
             A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
           msgs2' = [ r \in ROUNDS |->
             { D2(mm.src, r, mm.v): mm \in { m \in A1D: m.r = r } }
               \union { Q2(mm.src, r): mm \in { m \in A1Q: m.r = r } } ]
  PROVE  TypeOK'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
