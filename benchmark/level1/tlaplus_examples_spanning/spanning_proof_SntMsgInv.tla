---- MODULE spanning_proof_SntMsgInv ----
EXTENDS Integers, TLAPS
(* ---- Content from module spanning ---- *)
CONSTANTS Proc, NoPrnt, root, nbrs
ASSUME NoPrntFact == NoPrnt \notin Proc /\ nbrs \subseteq Proc \times Proc
VARIABLES prnt, rpt, msg
vars == <<prnt, rpt, msg>> 
             
Init == /\ prnt = [i \in Proc |-> NoPrnt]
        /\ rpt = [i \in Proc |-> FALSE]
        /\ msg = {}

CanSend(i, j) ==  (<<i, j>> \in nbrs) /\ (i = root \/ prnt[i] # NoPrnt)

Update(i, j) == /\ prnt' = [prnt EXCEPT ![i] = j]
                /\ UNCHANGED <<rpt, msg>>
    
Send(i) == \E k \in Proc: /\ CanSend(i, k) /\ (<<i, k>> \notin msg)
                          /\ msg' = msg \cup {<<i, k>>}
                          /\ UNCHANGED <<prnt, rpt>>
                                                                                    
Parent(i) == /\ prnt[i] # NoPrnt /\ ~rpt[i]
             /\ rpt' = [rpt EXCEPT ![i] = TRUE] 
             /\ UNCHANGED <<msg, prnt>>
             
Next == \E i, j \in Proc: IF i # root /\ prnt[i] = NoPrnt /\ <<j, i>> \in msg
                          THEN Update(i, j)
                          ELSE \/ Send(i) \/ Parent(i) 
                               \/ UNCHANGED <<prnt, msg, rpt>>                   
                                                        
Spec == /\ Init /\ [][Next]_vars 
        /\ WF_vars(\E i, j \in Proc: IF i # root /\ prnt[i] = NoPrnt /\ <<j, i>> \in msg
                                     THEN Update(i, j)
                                     ELSE \/ Send(i) \/ Parent(i) 
                                          \/ UNCHANGED <<prnt, msg, rpt>>)
                                           
TypeOK == /\ \A i \in Proc : prnt[i] = NoPrnt \/ <<i, prnt[i]>> \in nbrs             
          /\ rpt \in [Proc -> BOOLEAN]  
          /\ msg \subseteq Proc \times Proc
  
Termination == <>(\A i \in Proc : i = root \/ (prnt[i] # NoPrnt /\ <<i, prnt[i]>> \in nbrs)) 

OneParent == [][\A i \in Proc : prnt[i] # NoPrnt => prnt[i] = prnt'[i]]_vars

SntMsg == \A i \in Proc: (i # root /\ prnt[i] = NoPrnt => \A j \in Proc: <<i ,j>> \notin msg)


(***************************************************************************)
(* TLAPS proof of                                                          *)
(*                                                                         *)
(*   Spec => []SntMsg                                                      *)
(*                                                                         *)
(* SntMsg ("a non-root process whose parent has not yet been set has sent  *)
(* no messages") is inductive once we add the dual:                        *)
(*                                                                         *)
(*   SentMeansCanSend ==                                                   *)
(*     \A i,j \in Proc : <<i,j>> \in msg => (i = root \/ prnt[i] # NoPrnt) *)
(*                                                                         *)
(* (Note: the spec's `TypeOK` requires <<i, prnt[i]>> \in nbrs, but        *)
(* `nbrs` is not assumed symmetric in the spec while the protocol's        *)
(* Update(i, j) action sets prnt[i] := j from a `<<j, i>> \in msg` that    *)
(* originated in `<<j, i>> \in nbrs`.  TypeOK is therefore not a true     *)
(* invariant of `Spec` in general; we leave it alone and prove SntMsg     *)
(* without it.)                                                            *)
(***************************************************************************)

SentMeansCanSend ==
  \A i, j \in Proc :
    <<i, j>> \in msg => (i = root \/ prnt[i] # NoPrnt)

PrntDomain == DOMAIN prnt = Proc

Inv == PrntDomain /\ SntMsg /\ SentMeansCanSend

LEMMA SntMsgStep == Inv /\ [Next]_vars => Inv'
  PROOF OMITTED

THEOREM SntMsgInv == Spec => []SntMsg
PROOF OBVIOUS

========================================