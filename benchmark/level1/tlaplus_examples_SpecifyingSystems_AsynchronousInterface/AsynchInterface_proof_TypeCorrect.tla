---- MODULE AsynchInterface_proof_TypeCorrect ----
EXTENDS Naturals, TLAPS
(* ---- Content from module AsynchInterface ---- *)
CONSTANT  Data
VARIABLES val, rdy, ack

TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}
---------------------------------------------------------------
Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy

Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

Rcv  == /\ rdy # ack
        /\ ack' = 1 - ack
        /\ UNCHANGED <<val, rdy>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>
---------------------------------------------------------------
THEOREM Spec => []TypeInvariant

(***************************************************************************)
(* TLAPS proof of the theorem stated in AsynchInterface.tla.               *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

========================================