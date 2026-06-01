----------------------------- MODULE SimpleMutex_Safety -----------------------------
EXTENDS Integers, TLAPS

VARIABLES trying, pc

vars == << trying, pc >>

ProcSet == ({0,1})

Init == 
        /\ trying = [i \in {0,1} |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in {0,1} -> "a"]

a(self) == /\ pc[self] = "a"
           /\ trying' = [trying EXCEPT ![self] = TRUE]
           /\ pc' = [pc EXCEPT ![self] = "b"]

b(self) == /\ pc[self] = "b"
           /\ ~trying[1 - self]
           /\ pc' = [pc EXCEPT ![self] = "cs"]
           /\ UNCHANGED trying

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED trying

p(self) == a(self) \/ b(self) \/ cs(self)

Next == (\E self \in {0,1}: p(self))
           \/ 
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

----------------------------------------------------------------------

TypeOK == /\ trying \in [ProcSet -> BOOLEAN]
          /\ pc \in [ProcSet -> {"a", "b", "cs", "Done"}]

Inv == /\ TypeOK
       /\ \A self \in ProcSet :
             pc[self] \in {"b", "cs", "Done"} => trying[self]
       /\ MutualExclusion

LEMMA InitInv == Init => Inv
PROOF
  BY DEF Init, Inv, TypeOK, ProcSet, MutualExclusion

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
PROOF
  BY SMT DEF Inv, TypeOK, MutualExclusion, Next, p, a, b, cs, vars, ProcSet

THEOREM Safety == Spec => []MutualExclusion
PROOF
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1>3. Spec => []Inv
    BY <1>1, <1>2, PTL DEF Spec
  <1>4. Inv => MutualExclusion
    BY DEF Inv
  <1>5. QED
    BY <1>3, <1>4, PTL

=============================================================================
