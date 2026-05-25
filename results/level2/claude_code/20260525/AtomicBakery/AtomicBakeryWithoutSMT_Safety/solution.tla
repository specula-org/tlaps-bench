------------ MODULE AtomicBakeryWithoutSMT_Safety ----------------------------
(***************************************************************************)
(* The Atomic Bakery algorithm is a version of the bakery algorithm in     *)
(* which reading and writing of a process's number is an atomic operation. *)
(* The bakery algorithm originally appeared in:                            *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* This PlusCal version of the Atomic Bakery algorithm is one in which     *)
(* variables whose initial values are not used are initialized to          *)
(* arbitrary type-correct values.  It is good for proving correctness but  *)
(* not for model checking, because it produces an unnecessarily large      *)
(* number of reachable states.  If the variables were left uninitialized,  *)
(* the PlusCal translation would initialize them to a particular           *)
(* unspecified value.  This would complicate the proof because it would    *)
(* make the type-correctness invariant more complicated, but it would be   *)
(* efficient to model check.  We could write a version that is both easy   *)
(* to prove and efficient to model check by initializing the variables to  *)
(* particular type-correct values.                                         *)
(*                                                                         *)
(* The proofs in this module were written before TLAPS's SMT backend was   *)
(* implemented, and constitute indeed one of the first proofs ever carried *)
(* out using TLAPS. Much shorter proofs can be obtained using that backend *)
(* -- see module AtomicBakery in the same directory.                      *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANT P
ASSUME PsubsetNat == P \subseteq Nat

(*********************************************************************
--algorithm AtomicBakery {
variable num = [i \in P |-> 0], flag = [i \in P |-> FALSE];

process (p \in P)
  variables unread \in SUBSET P, 
            max \in Nat, 
            nxt \in P
{
p1: while (TRUE) {
      unread := P \ {self} ;
      max := 0;
      flag[self] := TRUE;
p2:   while (unread # {}) {
        with (i \in unread) { unread := unread \ {i};
                              if (num[i] > max) { max := num[i]; }
         }
       };
p3:   num[self] := max + 1;
p4:   flag[self] := FALSE;
      unread := P \ {self} ;
p5:   while (unread # {}) {
        with (i \in unread) { nxt := i ; };
        await ~ flag[nxt];
p6:     await \/ num[nxt] = 0
              \/ IF self > nxt THEN num[nxt] > num[self]
                               ELSE num[nxt] \geq num[self];
        unread := unread \ {nxt};
        } ;
p7:   skip ; \* critical section;
p8:  num[self] := 0;
 }}
}
*********************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES num, flag, pc, unread, max, nxt

vars == << num, flag, pc, unread, max, nxt >>

Init == (* Global variables *)
        /\ num = [i \in P |-> 0]
        /\ flag = [i \in P |-> FALSE]
        (* Process p *)
        /\ unread \in [P -> SUBSET P]
        /\ max \in [P -> Nat]
        /\ nxt \in [P -> P]
        /\ pc = [self \in P |-> "p1"]

p1(self) == /\ pc[self] = "p1"
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << num, nxt >>

p2(self) == /\ pc[self] = "p2"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            /\ unread' = [unread EXCEPT
                                            ![self] = unread[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT
                                                    ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED max
                       /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p3"]
                       /\ UNCHANGED << unread, max >>
            /\ UNCHANGED << num, flag, nxt >>

p3(self) == /\ pc[self] = "p3"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p4(self) == /\ pc[self] = "p4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, max, nxt >>

p5(self) == /\ pc[self] = "p5"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            nxt' = [nxt EXCEPT
                                      ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "p6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p7"]
                       /\ UNCHANGED nxt
            /\ UNCHANGED << num, flag, unread, max >>

p6(self) == /\ pc[self] = "p6"
            /\ \/ num[nxt[self]] = 0
               \/ IF self > nxt[self] THEN num[nxt[self]] > num[self]
                                      ELSE num[nxt[self]] >= num[self]
            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, flag, max, nxt >>

p7(self) == /\ pc[self] = "p7"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p8"]
            /\ UNCHANGED << num, flag, unread, max, nxt >>

p8(self) == /\ pc[self] = "p8"
            /\ num' = [num EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self) \/ p5(self)
              \/ p6(self) \/ p7(self) \/ p8(self)

Next == (\E self \in P: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in P: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in P: pc[self] = "Done")

\* END TRANSLATION

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "p7"
                                               /\ pc[j] = "p7"

-----------------------------------------------------------------------------
TypeOK == /\ num  \in [P -> Nat]
          /\ flag \in [P -> BOOLEAN]
          /\ unread \in [P -> SUBSET P]
          /\ \A i \in P :
                pc[i] \in {"p2", "p5", "p6"} => i \notin unread[i]
          /\ max \in [P -> Nat]
          /\ nxt \in [P -> P]
          /\ \A i \in P : (pc[i] = "p6") => nxt[i] # i
          /\ pc \in
              [P -> {"p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8"}]

GG(j, i) == IF j > i THEN num[i] > num[j]
                     ELSE num[i] >= num[j]

After(i, j) ==  /\ num[j] > 0
                /\ \/ pc[i] = "p1"
                   \/ /\ pc[i] = "p2"
                      /\ \/ j \in unread[i]
                         \/ max[i] >= num[j]
                   \/ /\ pc[i] = "p3"
                      /\ max[i] >= num[j]
                   \/ /\ pc[i] \in {"p4", "p5", "p6"}
                      /\ GG(j,i)
                      /\ (pc[i] \in {"p5", "p6"}) => (j \in unread[i])

IInv(i) ==
  /\ (num[i] = 0) <=> (pc[i] \in {"p1", "p2", "p3"})
  /\ flag[i] <=> (pc[i] \in {"p2", "p3", "p4"})
  /\ (pc[i] \in {"p5", "p6"}) =>
        \A j \in (P \ unread[i]) \ {i} : After(j, i)
  /\ /\ (pc[i] = "p6")
     /\ \/ (pc[nxt[i]] = "p2") /\ (i \notin unread[nxt[i]])
        \/ pc[nxt[i]] = "p3"
     => max[nxt[i]] >= num[i]
  /\ (pc[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)
Inv == TypeOK /\ \A i \in P : IInv(i)
-----------------------------------------------------------------------------









-----------------------------------------------------------------------------




(***************************************************************************)
(* The following lemma asserts that the predicate After(i,j) is preserved  *)
(* if none of the state components change in terms of which it is defined. *)
(***************************************************************************)



LEMMA InitInv == Init => Inv
  BY DEF Init, Inv, TypeOK, IInv, After, GG

LEMMA InvImpliesMutex == Inv => MutualExclusion
  BY DEF Inv, IInv, After, GG, MutualExclusion

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
<1> USE PsubsetNat DEF Inv, TypeOK, IInv, After, GG
<1>1. CASE UNCHANGED vars
   BY <1>1 DEF vars
<1>2. CASE \E self \in P : p(self)
   <2> SUFFICES ASSUME NEW self \in P, p(self) PROVE Inv'  BY <1>2
   <2>1. CASE p1(self)
      <3> USE <2>1 DEF p1
      <3>1. TypeOK'  OBVIOUS
      <3>2. ASSUME NEW i \in P PROVE IInv(i)'
         <4>1. CASE i = self  BY <4>1
         <4>2. CASE i # self  BY <4>2
         <4>3. QED  BY <4>1, <4>2
      <3>3. QED  BY <3>1, <3>2
   <2>2. CASE p2(self)
      <3> USE <2>2 DEF p2
      <3>1. TypeOK'
         <4>1. CASE unread[self] = {}  BY <4>1
         <4>2. CASE unread[self] # {}
            <5> PICK c \in unread[self] :
                   /\ unread' = [unread EXCEPT ![self] = unread[self] \ {c}]
                   /\ IF num[c] > max[self]
                         THEN max' = [max EXCEPT ![self] = num[c]]
                         ELSE max' = max
                BY <4>2
            <5>1. QED  BY <4>2
         <4>3. QED  BY <4>1, <4>2
      <3>2. ASSUME NEW i \in P PROVE IInv(i)'
         <4>1. CASE i = self  BY <4>1
         <4>2. CASE i # self
            <5>1. CASE unread[self] = {}  BY <4>2, <5>1
            <5>2. CASE unread[self] # {}
               <6> PICK c \in unread[self] :
                      /\ unread' = [unread EXCEPT ![self] = unread[self] \ {c}]
                      /\ IF num[c] > max[self]
                            THEN max' = [max EXCEPT ![self] = num[c]]
                            ELSE max' = max
                   BY <5>2
               <6>1. c \in P  BY <5>2
               <6>2. max'[self] >= max[self] /\ max'[self] >= num[c]  BY <5>2, <6>1
               <6>3. \A k \in P : k # self => max'[k] = max[k]  BY <6>1
               <6>4. unread'[self] = unread[self] \ {c}  OBVIOUS
               <6>5. pc'[self] = "p2"  BY <5>2
               <6>6. QED  BY <4>2, <5>2, <6>1, <6>2, <6>3, <6>4, <6>5
            <5>3. QED  BY <5>1, <5>2
         <4>3. QED  BY <4>1, <4>2
      <3>3. QED  BY <3>1, <3>2
   <2>3. CASE p3(self)
      <3> USE <2>3 DEF p3
      <3>1. TypeOK'  OBVIOUS
      <3>2. ASSUME NEW i \in P PROVE IInv(i)'
         <4>1. CASE i = self  BY <4>1
         <4>2. CASE i # self  BY <4>2
         <4>3. QED  BY <4>1, <4>2
      <3>3. QED  BY <3>1, <3>2
   <2>4. CASE p4(self)  BY <2>4 DEF p4
   <2>5. CASE p5(self)
      <3> USE <2>5 DEF p5
      <3>1. TypeOK'
         <4>1. CASE unread[self] = {}  BY <4>1
         <4>2. CASE unread[self] # {}
            <5> PICK c \in unread[self] : nxt' = [nxt EXCEPT ![self] = c]
                BY <4>2
            <5>1. c \in P  BY <4>2
            <5>2. self \notin unread[self]  BY <4>2
            <5>3. c # self  BY <5>2
            <5>4. pc' = [pc EXCEPT ![self] = "p6"]  BY <4>2
            <5>5. QED  BY <5>1, <5>3, <5>4
         <4>3. QED  BY <4>1, <4>2
      <3>2. ASSUME NEW i \in P PROVE IInv(i)'
         <4>1. CASE i = self  BY <4>1
         <4>2. CASE i # self  BY <4>2
         <4>3. QED  BY <4>1, <4>2
      <3>3. QED  BY <3>1, <3>2
   <2>6. CASE p6(self)
      <3> USE <2>6 DEF p6
      <3>1. TypeOK'  OBVIOUS
      <3>2. ASSUME NEW i \in P PROVE IInv(i)'
         <4>1. CASE i = self  BY <4>1
         <4>2. CASE i # self  BY <4>2
         <4>3. QED  BY <4>1, <4>2
      <3>3. QED  BY <3>1, <3>2
   <2>7. CASE p7(self)  BY <2>7 DEF p7
   <2>8. CASE p8(self)
      <3> USE <2>8 DEF p8
      <3>1. TypeOK'  OBVIOUS
      <3>2. ASSUME NEW i \in P PROVE IInv(i)'
         <4>1. CASE i = self  BY <4>1
         <4>2. CASE i # self  BY <4>2
         <4>3. QED  BY <4>1, <4>2
      <3>3. QED  BY <3>1, <3>2
   <2>9. QED  BY <2>1,<2>2,<2>3,<2>4,<2>5,<2>6,<2>7,<2>8 DEF p
<1>3. QED  BY <1>1, <1>2 DEF Next, vars

THEOREM Safety == Spec => [] MutualExclusion
<1>1. Init => Inv  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
<1>3. Inv => MutualExclusion  BY InvImpliesMutex
<1>4. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
