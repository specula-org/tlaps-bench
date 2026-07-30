---- MODULE EWD998_proof_EnabledSystem ----
EXTENDS EWD998_proof_EnabledSystemScaffold
USE NAssumption
LEMMA EnabledSystem ==
  ASSUME TypeOK, N > 1 \/ counter[0]=0
  PROVE  ENABLED <<System>>_vars
         <=> \/ /\ token.pos = 0 
                /\ token.color = "black" \/ color[0] = "black" \/ counter[0]+token.q > 0
             \/ \E i \in Node \ {0} : ~ active[i] /\ token.pos = i
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
