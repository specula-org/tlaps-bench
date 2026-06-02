---- MODULE Channel_proof_TypeCorrect ----
EXTENDS Naturals, TLAPS
(* ---- Content from module Channel ---- *)
CONSTANT Data
VARIABLE chan 

TypeInvariant  ==  chan \in [val : Data,  rdy : {0, 1},  ack : {0, 1}]
-----------------------------------------------------------------------
Init  ==  /\ TypeInvariant
          /\ chan.ack = chan.rdy 

Send(d) ==  /\ chan.rdy = chan.ack
            /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv     ==  /\ chan.rdy # chan.ack
            /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next  ==  (\E d \in Data : Send(d)) \/ Rcv

Spec  ==  Init /\ [][Next]_chan
-----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

(***************************************************************************)
(* TLAPS proof of the theorem stated in Channel.tla.                       *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

========================================