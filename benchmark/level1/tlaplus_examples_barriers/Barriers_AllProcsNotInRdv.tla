------------------------------- MODULE Barriers_AllProcsNotInRdv -------------------------------

EXTENDS TLAPS, Integers, FiniteSets, FiniteSetTheorems

CONSTANTS
  N

(**
--algorithm Barriers {
    variables
      lock = 1,   \* lock variable used for critical sections
      gate_1 = 0, \* semaphore for the first chamber
      gate_2 = 0, \* semaphore for the second chamber
      rdv = 0;    \* counts the processes entering/leaving the barrier

    macro Lock(l) {
        await l = 1;
        l := 0;
    }

    macro Unlock(l) {
        l := 1;
    }

    macro Wait(s) {
        await s > 0;
        s := s - 1;
    }

    macro Signal(s) {
        s := s + N;
    }

    \* The algorithm uses two waiting chambers which wait for all processes to
    \* to enter before allowing them to continue.
    \* The usage of two chambers ensures no process can leave the barrier and
    \* pass through the whole barrier again while blocking others inside.
    process (proc \in 1..N) {
a0:   while (TRUE) {
        skip; \* Some code
        \* first waiting chamber a1-a6
a1:     Lock(lock);
a2:     rdv := rdv + 1; \* protect read/write of shared variable with a lock
a3:     if (rdv = N) {
          \* when all processes are in the first chamber
a4:       Signal(gate_1);
          \* open the chamber
        };
a5:     Unlock(lock);
a6:     Wait(gate_1);
        \* second waiting chamber a7-a12
a7:     Lock(lock);
a8:     rdv := rdv - 1; \* protect read/write of shared variable with a lock
a9:     if (rdv = 0) {
          \* when all processes are in the second chamber
a10:      Signal(gate_2);
          \* open the chamber
        };
a11:    Unlock(lock);
a12:    Wait(gate_2);
      }
    }
}
**)
\* BEGIN TRANSLATION (chksum(pcal) = "7a2331f4" /\ chksum(tla) = "4cd2e9fd")
VARIABLES pc, lock, gate_1, gate_2, rdv

vars == << pc, lock, gate_1, gate_2, rdv >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ lock = 1
        /\ gate_1 = 0
        /\ gate_2 = 0
        /\ rdv = 0
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << lock, gate_1, gate_2, rdv >>

a1(self) == /\ pc[self] = "a1"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << gate_1, gate_2, rdv >>

a2(self) == /\ pc[self] = "a2"
            /\ rdv' = rdv + 1
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ UNCHANGED << lock, gate_1, gate_2 >>

a3(self) == /\ pc[self] = "a3"
            /\ IF rdv = N
                  THEN /\ pc' = [pc EXCEPT ![self] = "a4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << lock, gate_1, gate_2, rdv >>

a4(self) == /\ pc[self] = "a4"
            /\ gate_1' = gate_1 + N
            /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << lock, gate_2, rdv >>

a5(self) == /\ pc[self] = "a5"
            /\ lock' = 1
            /\ pc' = [pc EXCEPT ![self] = "a6"]
            /\ UNCHANGED << gate_1, gate_2, rdv >>

a6(self) == /\ pc[self] = "a6"
            /\ gate_1 > 0
            /\ gate_1' = gate_1 - 1
            /\ pc' = [pc EXCEPT ![self] = "a7"]
            /\ UNCHANGED << lock, gate_2, rdv >>

a7(self) == /\ pc[self] = "a7"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "a8"]
            /\ UNCHANGED << gate_1, gate_2, rdv >>

a8(self) == /\ pc[self] = "a8"
            /\ rdv' = rdv - 1
            /\ pc' = [pc EXCEPT ![self] = "a9"]
            /\ UNCHANGED << lock, gate_1, gate_2 >>

a9(self) == /\ pc[self] = "a9"
            /\ IF rdv = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "a10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a11"]
            /\ UNCHANGED << lock, gate_1, gate_2, rdv >>

a10(self) == /\ pc[self] = "a10"
             /\ gate_2' = gate_2 + N
             /\ pc' = [pc EXCEPT ![self] = "a11"]
             /\ UNCHANGED << lock, gate_1, rdv >>

a11(self) == /\ pc[self] = "a11"
             /\ lock' = 1
             /\ pc' = [pc EXCEPT ![self] = "a12"]
             /\ UNCHANGED << gate_1, gate_2, rdv >>

a12(self) == /\ pc[self] = "a12"
             /\ gate_2 > 0
             /\ gate_2' = gate_2 - 1
             /\ pc' = [pc EXCEPT ![self] = "a0"]
             /\ UNCHANGED << lock, gate_1, rdv >>

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3(self) \/ a4(self)
                 \/ a5(self) \/ a6(self) \/ a7(self) \/ a8(self)
                 \/ a9(self) \/ a10(self) \/ a11(self) \/ a12(self)

Next == (\E self \in 1..N: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

-------------------------------------------------------------------------------

TypeOK ==
  /\ lock \in {0, 1}
  /\ gate_1 \in Nat
  /\ gate_2 \in Nat
  /\ rdv \in Int
  /\ pc \in [ProcSet -> {"a0", "a1", "a2", "a3", "a4", "a5", "a6", 
            "a7", "a8", "a9", "a10", "a11", "a12"}]

lockcs(p) ==
  pc[p] \in {"a2", "a3", "a4", "a5", "a8", "a9", "a10", "a11"}
ProcsInLockCS ==
  {p \in ProcSet: lockcs(p)}

LockInv == 
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))
  /\ (\E p \in ProcSet: lockcs(p)) => lock = 0
  
rdvsection(p) ==
  pc[p] \in {"a3", "a4", "a5", "a6", "a7", "a8"}
ProcsInRdv ==
  {p \in ProcSet : rdvsection(p)}
  
barrier1(p) ==
  pc[p] \in {"a0", "a1", "a2", "a3", "a4", "a5", "a6"}
ProcsInB1 ==
  {p \in ProcSet : barrier1(p)}
  
barrier2(p) ==
  pc[p] \in {"a7", "a8", "a9", "a10", "a11", "a12"}
ProcsInB2 ==
  {p \in ProcSet : barrier2(p)}

Inv == 
  \* the semaphore values are kept between 0 and N
  /\ gate_1 \in 0..N
  /\ gate_2 \in 0..N
  \* rdv is the amount of processes in ]a2 ; a8]
  /\ rdv = Cardinality(ProcsInRdv) \* proves that rdv \in 0..N
  \* open gates mean that at least one process must be in the correct 
  \* waiting section
  /\ gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"}
  /\ gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"}
  \* at least one gate must be closed
  /\ (gate_1 = 0) \/ (gate_2 = 0)
  \* if one process in the first barrier (or about to enter), 
  \* then second barrier must be empty
  /\ (\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
      => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
  \* if one process in second barrier, then first barrier must be empty
  /\ (\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
      => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
  \* The value of gate_1 is bounded by the count of processes 
  \* in the first barrier
  /\ gate_1 =< Cardinality(ProcsInB1)
  \* if one process arrives at the first barrier, the first gate is locked
  /\ (\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
      => gate_1 = 0
  \* if one process is in a4, that means rdv is equal to N and 
  \* all other processes are waiting on gate_1
  /\ \A p \in ProcSet: pc[p] = "a4" => (
          /\ rdv = N
          /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
     )
  \* The value of gate_2 is bounded by the count of processes 
  \* in the second barrier
  /\ gate_2 =< Cardinality(ProcsInB2)
  \* if one process arrives at the second barrier, the second gate is locked
  /\ (\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
      => gate_2 = 0
  \* if one process is in a10, that means rdv is equal to 0 and 
  \* all other processes are waiting on gate_2
  /\ \A p \in ProcSet: pc[p] = "a10" => (
          /\ rdv = 0
          /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
     )

FlushInv ==
  /\ gate_1 > 0 => gate_1 = Cardinality(ProcsInB1)
  /\ gate_2 > 0 => gate_2 = Cardinality(ProcsInB2)

pc_translation(self) ==
  IF pc[self] \in {"a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8", "a9", "a10"}
    THEN "b1"
  ELSE IF pc[self] = "a0" 
    THEN "b0"
  ELSE IF gate_2 > 0
    THEN "b0"
  ELSE "b1"

B == INSTANCE Barrier WITH pc <- [p \in ProcSet |-> pc_translation(p)]
BSpec == B!Spec

-------------------------------------------------------------------------------

ASSUME N_Assumption == N \in Nat \ {0} 

LEMMA Typing == Spec => []TypeOK
  PROOF OMITTED

LEMMA LockExclusion == Spec => []LockInv
  PROOF OMITTED

LEMMA ProcSetSubSetsBound ==
    /\ IsFiniteSet(ProcsInRdv) /\ Cardinality(ProcsInRdv) \in 0..N
    /\ IsFiniteSet(ProcsInB1) /\ Cardinality(ProcsInB1) \in 0..N
    /\ IsFiniteSet(ProcsInB1)' /\ Cardinality(ProcsInB1)' \in 0..N
    /\ IsFiniteSet(ProcsInB2) /\ Cardinality(ProcsInB2) \in 0..N
    /\ IsFiniteSet(ProcsInB2)' /\ Cardinality(ProcsInB2)' \in 0..N
  PROOF OMITTED

LEMMA AllProcsInRdv == 
    (Cardinality(ProcsInRdv) = N) => (\A p \in ProcSet : rdvsection(p)) 
  PROOF OMITTED

LEMMA AllProcsNotInRdv ==
    (Cardinality(ProcsInRdv) = 0) => ~(\E p \in ProcSet : rdvsection(p))
PROOF OBVIOUS

===============================================================================