---- MODULE EWD840_proof_EnabledSystem ----
EXTENDS EWD840_proof_EnabledSystemScaffold
USE NAssumption
LEMMA EnabledSystem ==
    ASSUME TypeOK 
    PROVE  (ENABLED <<System>>_vars) <=> 
              \/ tpos = 0 /\ (tcolor = "black" \/ color[0] = "black")
              \/ tpos \in Node \ {0} /\ (~active[tpos] \/ tcolor = "black" \/ color[tpos] = "black")
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
