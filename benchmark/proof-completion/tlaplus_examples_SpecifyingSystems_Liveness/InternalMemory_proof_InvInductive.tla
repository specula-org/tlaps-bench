------------------------- MODULE InternalMemory_proof_InvInductive ----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*                                                                         *)
(*    THEOREM ISpec => []TypeInvariant                                     *)
(*                                                                         *)
(* stated in InternalMemory.tla.                                           *)
(*                                                                         *)
(* TypeInvariant alone is not inductive: in Do(p), the next-state          *)
(* expression accesses buf[p].adr / buf[p].op, which only makes sense      *)
(* when buf[p] is in MReq.  We strengthen TypeInvariant with               *)
(* BufConsistent, which records the buf typing for each value of ctl[p].  *)
(***************************************************************************)
EXTENDS InternalMemory, TLAPS

BufConsistent ==
  /\ \A p \in Proc : (ctl[p] = "rdy")  => (buf[p] \in Val \cup {NoVal})
  /\ \A p \in Proc : (ctl[p] = "busy") => (buf[p] \in MReq)
  /\ \A p \in Proc : (ctl[p] = "done") => (buf[p] \in Val \cup {NoVal})

Inv == TypeInvariant /\ BufConsistent

LEMMA InvInductive == ISpec => []Inv
PROOF OBVIOUS

============================================================================
