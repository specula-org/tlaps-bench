-------------------------- MODULE SequencesTheorems_LenDomain -------------------------
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
  PROOF OMITTED

THEOREM LenDomain == \A S :
                       \A s \in Seq(S) :
                         \A n \in Nat : DOMAIN s = 1..n => n = Len(s)
PROOF
<1> SUFFICES ASSUME NEW S,
                    NEW s \in Seq(S),
                    NEW n \in Nat,
                    DOMAIN s = 1..n
             PROVE  n = Len(s)
  OBVIOUS
<1>1. /\ Len(s) \in Nat
      /\ DOMAIN s = 1..Len(s)
  BY LenDef
<1>2. CASE n < Len(s)
  <2>1. Len(s) \in DOMAIN s BY <1>1, <1>2
  <2>2. Len(s) \in 1..n BY <2>1
  <2>3. FALSE BY <1>2, <2>2
  <2> QED BY <2>3
<1>3. CASE Len(s) < n
  <2>1. n \in DOMAIN s BY <1>3
  <2>2. n \in 1..Len(s) BY <1>1, <2>1
  <2>3. FALSE BY <1>3, <2>2
  <2> QED BY <2>3
<1>4. CASE n = Len(s)
  OBVIOUS
<1> QED BY <1>1, <1>2, <1>3, <1>4

=============================================================================
