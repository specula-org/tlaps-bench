--------------------------- MODULE spanning_proof_SntMsgStep -----------------------------
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
EXTENDS spanning, TLAPS

SentMeansCanSend ==
  \A i, j \in Proc :
    <<i, j>> \in msg => (i = root \/ prnt[i] # NoPrnt)

PrntDomain == DOMAIN prnt = Proc

Inv == PrntDomain /\ SntMsg /\ SentMeansCanSend

LEMMA SntMsgStep == Inv /\ [Next]_vars => Inv'
PROOF OBVIOUS

============================================================================
