-------------------------- MODULE SequencesTheorems_LenAxiom -------------------------
(***************************************************************************)
(* The proofs in this module were essentially written before TLAPS's SMT   *)
(* backend prover was implemented. That backend usually allows for much    *)
(* shorter proofs.                                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLAPS

AXIOM SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}

AXIOM LenDef == \A S : \A seq \in Seq(S) :
                     /\ Len(seq) \in Nat 
                     /\ DOMAIN seq = 1..Len(seq)

THEOREM LenAxiom == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ seq \in [1..Len(seq) -> S]
PROOF
<1>1. /\ Len(seq) \in Nat
      /\ DOMAIN seq = 1..Len(seq)
  BY LenDef
<1>2. seq \in UNION {[1..n -> S] : n \in Nat}
  BY SeqDef
<1>3. seq \in [1..Len(seq) -> S]
  BY <1>1, <1>2
<1>4. QED
  BY <1>1, <1>3

=============================================================================
