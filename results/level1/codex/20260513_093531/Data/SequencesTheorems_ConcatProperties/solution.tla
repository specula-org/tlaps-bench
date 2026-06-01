-------------------------- MODULE SequencesTheorems_ConcatProperties -------------------------
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
  PROOF OMITTED

AXIOM HeadDef == \A s : Head(s) = s[1]
AXIOM TailDef == \A s : Tail(s) = [i \in 1..(Len(s)-1) |-> s[i+1]]

AXIOM SubSeqDef ==
        \A s, m, n : SubSeq(s, m, n) = [i \in 1..(1+n-m) |-> s[i+m-1]]

THEOREM InitialSubSeq ==
   ASSUME NEW S,
          NEW s \in Seq(S),
          NEW j \in 0..Len(s)
   PROVE  /\ SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
          /\ SubSeq(s, 1, j) \in Seq(S)
          /\ Len(SubSeq(s, 1, j)) = j
  PROOF OMITTED

------------------------------------------------------------------
THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
  PROOF OMITTED

------------------------------------------------------------------
THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)
  PROOF OMITTED

------------------------------------------------------------------
THEOREM HeadAndTailOfSeq ==
   ASSUME NEW S,
          NEW seq \in Seq(S), seq # << >>
   PROVE  /\ Head(seq) \in S
          /\ Tail(seq) \in Seq(S)
  (*************************************************************************)
  (* Note: the way Tail is defined, Tail(<< >>) \in Seq(S) is actually     *)
  (* valid (because Tail(<< >>) = << >>).                                  *)
  (*************************************************************************)
  PROOF OMITTED

------------------------------------------------------------------
Remove(i, seq) == [j \in 1..(Len(seq)-1) |->
                                   IF j < i THEN seq[j] ELSE seq[j+1]]
THEOREM RemoveSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE   Remove(i, seq) \in Seq(S)
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(*                                    Append                               *)
(***************************************************************************)
THEOREM AppendDef ==
   ASSUME NEW S, NEW seq \in Seq(S), NEW elt
   PROVE  Append(seq, elt) =
                [i \in 1..(Len(seq)+1) |-> IF i \leq Len(seq) THEN seq[i]
                                                              ELSE elt]
  PROOF OMITTED

THEOREM AppendProperties ==
          \A S :
            \A seq \in Seq(S), elt \in S :
                /\ Append(seq, elt) \in Seq(S)
                /\ Len(Append(seq, elt)) = Len(seq)+1
                /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
                /\ Append(seq, elt)[Len(seq)+1] = elt
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)
THEOREM ConcatDef ==
           \A S: 
           \A s1, s2 \in Seq(S) : s1 \o s2 =
                         [i \in 1..(Len(s1)+Len(s2)) |->
                           IF i \leq Len(s1) THEN s1[i]
                                             ELSE s2[i-Len(s1)]]
  PROOF OMITTED

THEOREM ConcatProperties ==
           \A S :
             \A s1, s2 \in Seq(S) :
                 /\ s1 \o s2 \in Seq(S)
                 /\ Len(s1 \o s2) = Len(s1) + Len(s2)
PROOF
  <1>1. SUFFICES ASSUME NEW S,
                       NEW s1 \in Seq(S),
                       NEW s2 \in Seq(S)
                PROVE  /\ s1 \o s2 \in Seq(S)
                       /\ Len(s1 \o s2) = Len(s1) + Len(s2)
    OBVIOUS
  <1>2. DEFINE n1 == Len(s1)
                 n2 == Len(s2)
  <1>3. n1 \in Nat /\ n2 \in Nat
    BY LenAxiom
  <1>4. n1 + n2 \in Nat
    BY <1>3
  <1>5. s1 \o s2 = [i \in 1..(n1+n2) |->
                       IF i \leq n1 THEN s1[i]
                                         ELSE s2[i-n1]]
    BY ConcatDef
  <1>6. \A i \in 1..(n1+n2) : i \leq n1 => s1[i] \in S
    BY ElementOfSeq
  <1>7. \A i \in 1..(n1+n2) : ~(i \leq n1) => s2[i-n1] \in S
  PROOF
    <2>1. SUFFICES ASSUME NEW i \in 1..(n1+n2),
                           ~(i \leq n1)
                     PROVE  s2[i-n1] \in S
      OBVIOUS
    <2>2. i \in Int /\ n1 \in Int /\ n2 \in Int
      BY <1>3, <2>1
    <2>3. n1 < i
      BY <2>1, <2>2, SMT
    <2>4. i \leq n1 + n2
      BY <2>1, <2>2, SMT
    <2>5. 1 \leq i - n1
      BY <2>2, <2>3, SMT
    <2>6. i - n1 \leq n2
      BY <2>2, <2>4, SMT
    <2>7. i - n1 \in Int
      BY <2>2, SMT
    <2>8. i - n1 \in 1..n2
      BY <2>5, <2>6, <2>7
    <2>9. QED
      BY <2>8, ElementOfSeq
  <1>8. \A i \in 1..(n1+n2) :
           (IF i \leq n1 THEN s1[i] ELSE s2[i-n1]) \in S
    BY <1>6, <1>7
  <1>9. [i \in 1..(n1+n2) |->
           IF i \leq n1 THEN s1[i]
                             ELSE s2[i-n1]] \in Seq(S)
    BY <1>4, <1>8, SeqDef
  <1>10. s1 \o s2 \in Seq(S)
    BY <1>5, <1>9
  <1>11. DOMAIN (s1 \o s2) = 1..(n1+n2)
    BY <1>5
  <1>12. Len(s1 \o s2) = n1 + n2
    BY <1>4, <1>10, <1>11, LenDomain
  <1>13. QED
    BY <1>10, <1>12 DEF n1, n2

=============================================================================
