---- MODULE AlternatingBit_proof_TypeCorrect ----
EXTENDS Naturals, Sequences, TLAPS
(* ---- Content from module AlternatingBit ---- *)
CONSTANTS Data
VARIABLES msgQ, 
          ackQ, 
          sBit, 
          sAck, 
          rBit, 
          sent, 
          rcvd  
-----------------------------------------------------------------------------
ABInit == /\ msgQ = << >>
          /\ ackQ = << >>
          /\ sBit \in {0, 1}
          /\ sAck = sBit
          /\ rBit = sBit
          /\ sent \in Data
          /\ rcvd \in Data

ABTypeInv == /\ msgQ \in Seq({0,1} \X Data)
             /\ ackQ \in Seq({0,1})
             /\ sBit \in {0, 1}
             /\ sAck \in {0, 1}
             /\ rBit \in {0, 1}
             /\ sent \in Data
             /\ rcvd \in Data
-----------------------------------------------------------------------------
SndNewValue(d) == 
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ msgQ' = Append(msgQ, <<sBit', d>>) 
  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

ReSndMsg == 
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, <<sBit, sent>>)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

RcvMsg == 
  /\ msgQ # <<>>
  /\ msgQ' = Tail(msgQ)
  /\ rBit' = Head(msgQ)[1] 
  /\ rcvd' = Head(msgQ)[2] 
  /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

SndAck == /\ ackQ' = Append(ackQ, rBit)
          /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

RcvAck == /\ ackQ # << >>
          /\ ackQ' = Tail(ackQ)
          /\ sAck' = Head(ackQ)
          /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

Lose(q) == 
   /\ q # << >>
   /\ \E i \in 1..Len(q) : 
          q' = [j \in 1..(Len(q)-1) |-> IF j < i THEN q[j] 
                                                 ELSE q[j+1] ]
   /\ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ

LoseAck == Lose(ackQ) /\ UNCHANGED msgQ

ABNext == \/  \E d \in Data : SndNewValue(d) 
          \/  ReSndMsg \/ RcvMsg \/ SndAck \/ RcvAck 
          \/  LoseMsg \/ LoseAck 
-----------------------------------------------------------------------------
abvars == << msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

ABFairness == /\ WF_abvars(ReSndMsg) /\ WF_abvars(SndAck)   
              /\ SF_abvars(RcvMsg) /\ SF_abvars(RcvAck) 
-----------------------------------------------------------------------------
ABSpec == ABInit /\ [][ABNext]_abvars /\ ABFairness
-----------------------------------------------------------------------------
THEOREM ABSpec => []ABTypeInv

(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM ABSpec => []ABTypeInv                                         *)
(* stated in AlternatingBit.tla.                                           *)
(***************************************************************************)

LEMMA AppendType ==
  ASSUME NEW T, NEW s \in Seq(T), NEW e \in T
  PROVE  Append(s, e) \in Seq(T)
  OBVIOUS

LEMMA TailType ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Tail(s) \in Seq(T)
  OBVIOUS

LEMMA HeadType ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Head(s) \in T
  OBVIOUS

LEMMA LosePreservesType ==
  ASSUME NEW T, NEW q \in Seq(T), q # << >>,
         NEW i \in 1..Len(q),
         NEW q2,
         q2 = [j \in 1..(Len(q)-1) |-> IF j < i THEN q[j] ELSE q[j+1]]
  PROVE  q2 \in Seq(T)
  OBVIOUS

THEOREM TypeCorrect == ABSpec => []ABTypeInv
PROOF OBVIOUS

========================================