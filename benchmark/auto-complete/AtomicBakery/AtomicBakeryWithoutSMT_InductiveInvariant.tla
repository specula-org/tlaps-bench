------------ MODULE AtomicBakeryWithoutSMT_InductiveInvariant ----------------------------
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
EXTENDS AtomicBakeryWithoutSMT

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

Termination == <>(\A self \in P: pc[self] = "Done")

\* END TRANSLATION

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "p7"
                                               /\ pc[j] = "p7"

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

THEOREM GTAxiom  == \A n, m \in Nat : ~ (n > m /\ m > n)
  OBVIOUS (*{ by (isabelle "(auto dest: nat_less_trans)") }*)

THEOREM GEQAxiom == \A n, m \in Nat : (n = m) \/ n > m \/ m > n
  OBVIOUS (*{ by (isabelle "(auto elim: nat_less_cases)") }*)

THEOREM GEQTransitive == \A n, m, q \in Nat : n >= m /\ m >= q => n >= q
  OBVIOUS (*{ by (isabelle "(auto dest: nat_leq_trans)") }*)

THEOREM Transitivity2 == \A n, m, q \in Nat : n > m /\ m >= q => n > q
  OBVIOUS (*{ by (isabelle "(auto dest: nat_leq_less_trans)") }*)

THEOREM GEQorLT == \A n, m \in Nat : n >= m <=> ~(m > n)
  OBVIOUS (*{ by (isabelle "(auto simp: nat_not_less[simplified])") }*)

THEOREM NatGEQZero == \A n \in Nat: (n > 0) <=> (n # 0)
  OBVIOUS (*{ by (isabelle "(auto simp: nat_gt0_not0)") }*)

THEOREM Plus1 == \A n \in Nat: n+1 \in Nat /\ n+1 # 0
  OBVIOUS

THEOREM GGIrreflexive == ASSUME NEW i \in P,
                                NEW j \in P,
                                i # j,
                                num[i] \in Nat,
                                num[j] \in Nat
                         PROVE  ~ (GG(i, j) /\ GG(j, i))
PROOF OMITTED

THEOREM InitImpliesTypeOK == 
  ASSUME Init
  PROVE  TypeOK
PROOF OMITTED

THEOREM TypeOKInvariant ==
        ASSUME TypeOK,
               Next
        PROVE  TypeOK'
PROOF OMITTED

THEOREM InitInv == Init => Inv
PROOF OMITTED

THEOREM InvExclusion == Inv => MutualExclusion
PROOF OMITTED

(***************************************************************************)
(* The following lemma asserts that the predicate After(i,j) is preserved  *)
(* if none of the state components change in terms of which it is defined. *)
(***************************************************************************)
THEOREM AfterPrime == 
  ASSUME NEW i, NEW j,
         After(i,j),
         UNCHANGED <<num[i], num[j], pc[i], unread[i], max[i]>>
  PROVE  After(i, j)'
PROOF OMITTED

THEOREM InductiveInvariant == Inv /\ Next => Inv'
PROOF OBVIOUS

=============================================================================
