--------------------------- MODULE Peterson_MutualExclusion  ----------------------------

EXTENDS TLAPS

Not(i) == IF i = 0 THEN 1 ELSE 0

VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init == 
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << flag, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ turn' = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Not(self)
            /\ pc' = [pc EXCEPT ![self] = "a3a"]
            /\ flag' = flag

a3a(self) == /\ pc[self] = "a3a"
             /\ IF flag[Not(self)]
                   THEN /\ pc' = [pc EXCEPT ![self] = "a3b"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

a3b(self) == /\ pc[self] = "a3b"
             /\ IF turn = Not(self)
                   THEN /\ pc' = [pc EXCEPT ![self] = "a3a"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << flag, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ turn' = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3a(self) \/ a3b(self)
                 \/ cs(self) \/ a4(self)

Next == (\E self \in {0,1}: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(proc(self))

MutualExclusion == ~(pc[0] = "cs"  /\ pc[1] = "cs")

-----------------------------------------------------------------------------

USE DEF ProcSet

Labels == {"a0", "a1", "a2", "a3a", "a3b", "cs", "a4"}

FlagSet == {"a2", "a3a", "a3b", "cs", "a4"}

CritSet == {"cs", "a4"}

WaitSet == {"a3b", "cs", "a4"}

IndInv ==
        /\ flag \in [ProcSet -> BOOLEAN]
        /\ turn \in ProcSet
        /\ pc \in [ProcSet -> Labels]
        /\ \A self \in ProcSet :
              pc[self] \in FlagSet => flag[self]
        /\ \A self \in ProcSet :
              /\ pc[self] \in CritSet
              /\ pc[Not(self)] \in WaitSet
              => turn = self
        /\ \A self \in ProcSet :
              /\ pc[self] = "a3a"
              /\ pc[Not(self)] \in CritSet
              => turn = Not(self)

LEMMA InitIndInv == Init => IndInv
PROOF BY SMT DEF Init, IndInv, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

LEMMA a0IndInv == \A self \in ProcSet : IndInv /\ a0(self) => IndInv'
PROOF BY SMT DEF IndInv, a0, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

LEMMA a1IndInv == \A self \in ProcSet : IndInv /\ a1(self) => IndInv'
PROOF BY SMT DEF IndInv, a1, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

LEMMA a2IndInv == \A self \in ProcSet : IndInv /\ a2(self) => IndInv'
PROOF BY SMT DEF IndInv, a2, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

LEMMA a3aIndInv == \A self \in ProcSet : IndInv /\ a3a(self) => IndInv'
PROOF BY SMT DEF IndInv, a3a, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

LEMMA a3bIndInv == \A self \in ProcSet : IndInv /\ a3b(self) => IndInv'
PROOF BY SMT DEF IndInv, a3b, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

LEMMA csIndInv == \A self \in ProcSet : IndInv /\ cs(self) => IndInv'
PROOF BY SMT DEF IndInv, cs, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

LEMMA a4IndInv == \A self \in ProcSet : IndInv /\ a4(self) => IndInv'
PROOF BY SMT DEF IndInv, a4, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

LEMMA procIndInv == \A self \in ProcSet : IndInv /\ proc(self) => IndInv'
PROOF BY a0IndInv, a1IndInv, a2IndInv, a3aIndInv, a3bIndInv, csIndInv, a4IndInv DEF proc

LEMMA NextIndInv == IndInv /\ Next => IndInv'
PROOF BY procIndInv DEF Next, ProcSet

LEMMA StutterIndInv == IndInv /\ vars' = vars => IndInv'
PROOF BY SMT DEF IndInv, vars

LEMMA ActionIndInv == IndInv /\ [Next]_vars => IndInv'
PROOF BY NextIndInv, StutterIndInv DEF Next, vars

LEMMA InvImpliesMutualExclusion == IndInv => MutualExclusion
PROOF BY SMT DEF IndInv, MutualExclusion, Labels, FlagSet, CritSet, WaitSet, ProcSet, Not

THEOREM Spec => []MutualExclusion
PROOF
  <1>. USE InitIndInv, ActionIndInv, InvImpliesMutualExclusion DEF Spec
  <1>. QED BY PTL

-----------

=============================================================================
