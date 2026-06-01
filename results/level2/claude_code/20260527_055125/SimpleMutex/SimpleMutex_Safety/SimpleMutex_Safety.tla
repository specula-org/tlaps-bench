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

IndInv ==
  /\ pc \in [{0,1} -> {"a", "b", "cs", "Done"}]
  /\ trying \in [{0,1} -> BOOLEAN]
  /\ \A i \in {0,1}: (pc[i] = "a") <=> (trying[i] = FALSE)
  /\ \A i \in {0,1}: (pc[i] = "cs" \/ pc[i] = "Done") => (pc[1-i] = "a" \/ pc[1-i] = "b")

LEMMA InitIndInv == Init => IndInv
  BY DEF Init, IndInv, ProcSet

LEMMA IndInvIsInductive == IndInv /\ [Next]_vars => IndInv'
  <1> SUFFICES ASSUME IndInv, [Next]_vars PROVE IndInv'
    OBVIOUS
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars, IndInv
  <1>2. ASSUME NEW self \in {0,1}, a(self) PROVE IndInv'
    BY <1>2 DEF a, IndInv
  <1>3. ASSUME NEW self \in {0,1}, b(self) PROVE IndInv'
    BY <1>3 DEF b, IndInv
  <1>4. ASSUME NEW self \in {0,1}, cs(self) PROVE IndInv'
    BY <1>4 DEF cs, IndInv
  <1>5. CASE (\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars
    BY <1>5 DEF vars, IndInv
  <1>6. QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, p

LEMMA IndInvImpliesME == IndInv => MutualExclusion
  BY DEF IndInv, MutualExclusion

THEOREM Safety == Spec => []MutualExclusion
PROOF
  <1>1. Init => IndInv BY InitIndInv
  <1>2. IndInv /\ [Next]_vars => IndInv' BY IndInvIsInductive
  <1>3. IndInv => MutualExclusion BY IndInvImpliesME
  <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
