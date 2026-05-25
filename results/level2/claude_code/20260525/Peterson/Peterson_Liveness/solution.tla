--------------------------- MODULE Peterson_Liveness  ----------------------------
(***********************************************************************)
(* This is Peterson's standard two-process mutual exclusion algorithm. *)
(* A TLA+ specification is derived from a PlusCal algorithm, then      *)
(* mutual exclusion is shown using either the SMT backend or just the  *)
(* Zenon and Isabelle backends.                                        *)
(* This example is described in more detail in:                        *)
(* D. Cousineau et al.: TLA+ Proofs. 18th Intl. Symp. Formal Methods   *)
(* (FM 2012). Springer LNCS 7436, pp. 147-154, Paris 2012.             *)
(* Available online at http://www.loria.fr/~merz/papers/fm2012.html    *)
(***********************************************************************)
EXTENDS TLAPS

Not(i) == IF i = 0 THEN 1 ELSE 0

(*******
--algorithm Peterson {
   variables flag = [i \in {0, 1} |-> FALSE], turn = 0;
   fair process (proc \in {0,1}) {
     a0: while (TRUE) {
     a1:   flag[self] := TRUE;
     a2:   turn := Not(self);
     a3a:  if (flag[Not(self)]) {goto a3b} else {goto cs} ;
     a3b:  if (turn = Not(self)) {goto a3a} else {goto cs} ;
     cs:   skip;  \* critical section
     a4:   flag[self] := FALSE;
     } \* end while
    } \* end process
  }
********)

\* BEGIN TRANSLATION
VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
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

\* END TRANSLATION

\* The following predicate defines mutual exclusion of Peterson's algorithm.
MutualExclusion == ~(pc[0] = "cs"  /\ pc[1] = "cs")

NeverCS == pc[0] # "cs"

Wait(i) == (pc[0] = "a3a") \/ (pc[0] = "a3b")
CS(i) == pc[i] = "cs"
Fairness == WF_vars(proc(0)) /\ WF_vars(proc(1))
FairSpec == Spec /\ Fairness
Liveness1 == []<>CS(0)
Liveness == (Wait(0) ~> CS(0)) /\ (Wait(1) ~> CS(1))

-----------------------------------------------------------------------------

\* The proof

TypeOK == /\ pc \in [{0,1} -> {"a0", "a1", "a2", "a3a", "a3b", "cs", "a4"}]
          /\ turn \in {0, 1}
          /\ flag \in [{0,1} -> BOOLEAN]

I == \A i \in {0, 1} :
       /\ (pc[i] \in {"a2", "a3a", "a3b", "cs", "a4"} => flag[i])
       /\ (pc[i] \in {"cs", "a4"})
            => /\ pc[Not(i)] \notin {"cs", "a4"}
               /\ (pc[Not(i)] \in {"a3a", "a3b"}) => (turn = i)

Inv == TypeOK /\ I

\* Use this specification to check with TLC that Inv is an inductive invariant.
ISpec == Inv /\ [][Next]_vars

USE DEF ProcSet

\* First proof, using SMT for showing that Inv is inductive



\* Second proof, using just Zenon and Isabelle

-----------

 \*(flag[1] \/ turn = 1)
Q1 == CS(0)

\* Liveness proof

\* ===================================================================
\* Scaffolding for the liveness proof.
\* ===================================================================

\* A weakened inductive invariant that suffices for liveness: the type
\* invariant plus the fact that a process has raised its flag exactly while
\* it is in the "active" part of the protocol.
InvL == /\ TypeOK
        /\ \A k \in {0,1} : pc[k] \in {"a2","a3a","a3b","cs","a4"} => flag[k]

\* Next-state action enriched with the invariant (so WF1 obligations carry it).
Nxt == Next /\ InvL /\ InvL'

\* Process i is busy-waiting at a3a/a3b.
W(i) == pc[i] = "a3a" \/ pc[i] = "a3b"

\* Sub-case-B stage predicate: i waits, turn favours the other process j,
\* and j is at location L (j progresses through its loop until it flips turn).
BB(i, L) == W(i) /\ turn = Not(i) /\ pc[Not(i)] = L

\* Guard operators (each = InvL /\ a state predicate) used as the WF1 "P".
GFwd(i, L) == InvL /\ pc[i] = L
GTrn(i, L) == InvL /\ pc[i] = L /\ turn = i
GBb(i, L)  == InvL /\ W(i) /\ turn = Not(i) /\ pc[Not(i)] = L

LEMMA NotType == \A i \in {0,1} : /\ Not(i) \in {0,1}
                                  /\ Not(i) # i
                                  /\ Not(Not(i)) = i
  BY DEF Not

LEMMA InvL_Lemma == Spec => []InvL
<1>1. Init => InvL  BY DEF Init, InvL, TypeOK
<1>2. InvL /\ [Next]_vars => InvL'
  <2> SUFFICES ASSUME InvL, [Next]_vars PROVE InvL'  OBVIOUS
  <2>1. CASE vars' = vars  BY <2>1 DEF InvL, TypeOK, vars
  <2>2. CASE Next
    <3> SUFFICES ASSUME NEW p \in {0,1}, proc(p) PROVE InvL'  BY <2>2 DEF Next
    <3> QED  BY SMT DEF InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
  <2> QED BY <2>1, <2>2 DEF Next, vars
<1> QED BY <1>1, <1>2, PTL DEF Spec

LEMMA Nxt_Lemma == Spec => [][Nxt]_vars
<1>1. InvL /\ InvL' /\ [Next]_vars => [Nxt]_vars  BY DEF Nxt, vars
<1> QED BY InvL_Lemma, <1>1, PTL DEF Spec

\* ----- forward steps of process i (always-enabled local progress) -----

LEMMA L_a0 == ASSUME NEW i \in {0,1}
              PROVE Spec => ((pc[i]="a0") ~> (pc[i]="a1"))
<1>1. GFwd(i,"a0") /\ [Nxt]_vars => (GFwd(i,"a0")' \/ (pc[i]="a1")')
  BY NotType DEF GFwd, Nxt, Next, InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GFwd(i,"a0") /\ <<proc(i)>>_vars => (pc[i]="a1")'
  BY DEF GFwd, InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars
<1>3. GFwd(i,"a0") => ENABLED <<proc(i)>>_vars
  <2> SUFFICES ASSUME GFwd(i,"a0") PROVE ENABLED <<proc(i)>>_vars  OBVIOUS
  <2>1. pc[i] = "a0" /\ TypeOK  BY DEF GFwd, InvL
  <2> DEFINE q == [pc EXCEPT ![i] = "a1"]
  <2>2. q # pc  BY <2>1 DEF TypeOK
  <2> QED BY <2>1, <2>2, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK
<1>wf. Spec => WF_vars(proc(i))  BY DEF Spec
<1>4. Spec => (GFwd(i,"a0") ~> (pc[i]="a1"))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GFwd

LEMMA L_a1 == ASSUME NEW i \in {0,1}
              PROVE Spec => ((pc[i]="a1") ~> (pc[i]="a2"))
<1>1. GFwd(i,"a1") /\ [Nxt]_vars => (GFwd(i,"a1")' \/ (pc[i]="a2")')
  BY NotType DEF GFwd, Nxt, Next, InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GFwd(i,"a1") /\ <<proc(i)>>_vars => (pc[i]="a2")'
  BY DEF GFwd, InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars
<1>3. GFwd(i,"a1") => ENABLED <<proc(i)>>_vars
  <2> SUFFICES ASSUME GFwd(i,"a1") PROVE ENABLED <<proc(i)>>_vars  OBVIOUS
  <2>1. pc[i] = "a1" /\ TypeOK  BY DEF GFwd, InvL
  <2> DEFINE q == [pc EXCEPT ![i] = "a2"]
  <2>2. q # pc  BY <2>1 DEF TypeOK
  <2> QED BY <2>1, <2>2, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK
<1>wf. Spec => WF_vars(proc(i))  BY DEF Spec
<1>4. Spec => (GFwd(i,"a1") ~> (pc[i]="a2"))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GFwd

LEMMA L_a2 == ASSUME NEW i \in {0,1}
              PROVE Spec => ((pc[i]="a2") ~> (pc[i]="a3a"))
<1>1. GFwd(i,"a2") /\ [Nxt]_vars => (GFwd(i,"a2")' \/ (pc[i]="a3a")')
  BY NotType DEF GFwd, Nxt, Next, InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GFwd(i,"a2") /\ <<proc(i)>>_vars => (pc[i]="a3a")'
  BY DEF GFwd, InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars
<1>3. GFwd(i,"a2") => ENABLED <<proc(i)>>_vars
  <2> SUFFICES ASSUME GFwd(i,"a2") PROVE ENABLED <<proc(i)>>_vars  OBVIOUS
  <2>1. pc[i] = "a2" /\ TypeOK  BY DEF GFwd, InvL
  <2> DEFINE q == [pc EXCEPT ![i] = "a3a"]
  <2>2. q # pc  BY <2>1 DEF TypeOK
  <2> QED BY <2>1, <2>2, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK
<1>wf. Spec => WF_vars(proc(i))  BY DEF Spec
<1>4. Spec => (GFwd(i,"a2") ~> (pc[i]="a3a"))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GFwd

LEMMA L_a4 == ASSUME NEW i \in {0,1}
              PROVE Spec => ((pc[i]="a4") ~> (pc[i]="a0"))
<1>1. GFwd(i,"a4") /\ [Nxt]_vars => (GFwd(i,"a4")' \/ (pc[i]="a0")')
  BY NotType DEF GFwd, Nxt, Next, InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GFwd(i,"a4") /\ <<proc(i)>>_vars => (pc[i]="a0")'
  BY DEF GFwd, InvL, TypeOK, proc, a0,a1,a2,a3a,a3b,cs,a4, vars
<1>3. GFwd(i,"a4") => ENABLED <<proc(i)>>_vars
  <2> SUFFICES ASSUME GFwd(i,"a4") PROVE ENABLED <<proc(i)>>_vars  OBVIOUS
  <2>1. pc[i] = "a4" /\ TypeOK  BY DEF GFwd, InvL
  <2> DEFINE q == [pc EXCEPT ![i] = "a0"]
  <2>2. q # pc  BY <2>1 DEF TypeOK
  <2> QED BY <2>1, <2>2, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK
<1>wf. Spec => WF_vars(proc(i))  BY DEF Spec
<1>4. Spec => (GFwd(i,"a4") ~> (pc[i]="a0"))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GFwd

\* ----- sub-case A: turn favours i, so i marches into the critical section -----

LEMMA L_Aa3b == ASSUME NEW i \in {0,1}
   PROVE Spec => ((pc[i]="a3b" /\ turn=i) ~> CS(i))
<1>1. GTrn(i,"a3b") /\ [Nxt]_vars => (GTrn(i,"a3b")' \/ CS(i)')
  BY NotType DEF GTrn, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GTrn(i,"a3b") /\ <<proc(i)>>_vars => CS(i)'
  BY NotType DEF GTrn, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GTrn(i,"a3b") => ENABLED <<proc(i)>>_vars
  <2> SUFFICES ASSUME GTrn(i,"a3b") PROVE ENABLED <<proc(i)>>_vars  OBVIOUS
  <2>0. pc[i]="a3b" /\ turn=i /\ TypeOK  BY DEF GTrn, InvL
  <2>1. turn # Not(i)  BY <2>0, NotType
  <2> DEFINE q == [pc EXCEPT ![i] = "cs"]
  <2>2. q # pc  BY <2>0 DEF TypeOK
  <2> QED BY <2>0, <2>1, <2>2, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK
<1>wf. Spec => WF_vars(proc(i))  BY DEF Spec
<1>4. Spec => (GTrn(i,"a3b") ~> CS(i))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GTrn

LEMMA L_Aa3a == ASSUME NEW i \in {0,1}
   PROVE Spec => ((pc[i]="a3a" /\ turn=i) ~> ((pc[i]="a3b" /\ turn=i) \/ CS(i)))
<1>1. GTrn(i,"a3a") /\ [Nxt]_vars => (GTrn(i,"a3a")' \/ ((pc[i]="a3b" /\ turn=i)' \/ CS(i)'))
  BY NotType DEF GTrn, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GTrn(i,"a3a") /\ <<proc(i)>>_vars => ((pc[i]="a3b" /\ turn=i)' \/ CS(i)')
  BY NotType DEF GTrn, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GTrn(i,"a3a") => ENABLED <<proc(i)>>_vars
  <2> SUFFICES ASSUME GTrn(i,"a3a") PROVE ENABLED <<proc(i)>>_vars  OBVIOUS
  <2>0. pc[i]="a3a" /\ TypeOK  BY DEF GTrn, InvL
  <2>a. CASE flag[Not(i)]
    <3> DEFINE q == [pc EXCEPT ![i] = "a3b"]
    <3>1. q # pc  BY <2>0 DEF TypeOK
    <3> QED BY <2>0, <2>a, <3>1, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK
  <2>b. CASE ~flag[Not(i)]
    <3> DEFINE q == [pc EXCEPT ![i] = "cs"]
    <3>1. q # pc  BY <2>0 DEF TypeOK
    <3> QED BY <2>0, <2>b, <3>1, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK
  <2> QED BY <2>a, <2>b
<1>wf. Spec => WF_vars(proc(i))  BY DEF Spec
<1>4. Spec => (GTrn(i,"a3a") ~> ((pc[i]="a3b" /\ turn=i) \/ CS(i)))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GTrn

LEMMA C_A == ASSUME NEW i \in {0,1}
   PROVE Spec => ((W(i) /\ turn=i) ~> CS(i))
<1>1. Spec => ((pc[i]="a3a" /\ turn=i) ~> ((pc[i]="a3b" /\ turn=i) \/ CS(i)))  BY L_Aa3a
<1>2. Spec => ((pc[i]="a3b" /\ turn=i) ~> CS(i))  BY L_Aa3b
<1> QED BY <1>1, <1>2, PTL DEF W, CS

\* ----- sub-case B: turn favours j; j runs its loop and eventually flips turn -----

LEMMA L_Ba2 == ASSUME NEW i \in {0,1}
   PROVE Spec => (BB(i,"a2") ~> ((W(i) /\ turn=i) \/ CS(i)))
<1>1. GBb(i,"a2") /\ [Nxt]_vars => (GBb(i,"a2")' \/ ((W(i) /\ turn=i)' \/ CS(i)'))
  BY NotType DEF GBb, BB, W, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GBb(i,"a2") /\ <<proc(Not(i))>>_vars => ((W(i) /\ turn=i)' \/ CS(i)')
  BY NotType DEF GBb, BB, W, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GBb(i,"a2") => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME GBb(i,"a2") PROVE ENABLED <<proc(Not(i))>>_vars  OBVIOUS
  <2>0. pc[Not(i)]="a2" /\ TypeOK  BY NotType DEF GBb, InvL
  <2> DEFINE q == [pc EXCEPT ![Not(i)] = "a3a"]
  <2>1. q # pc  BY <2>0, NotType DEF TypeOK
  <2> QED BY <2>0, <2>1, NotType, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK, Not
<1>wf. Spec => WF_vars(proc(Not(i)))  BY NotType DEF Spec
<1>4. Spec => (GBb(i,"a2") ~> ((W(i) /\ turn=i) \/ CS(i)))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GBb, BB

LEMMA L_Ba1 == ASSUME NEW i \in {0,1}
   PROVE Spec => (BB(i,"a1") ~> (BB(i,"a2") \/ CS(i)))
<1>1. GBb(i,"a1") /\ [Nxt]_vars => (GBb(i,"a1")' \/ (BB(i,"a2")' \/ CS(i)'))
  BY NotType DEF GBb, BB, W, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GBb(i,"a1") /\ <<proc(Not(i))>>_vars => (BB(i,"a2")' \/ CS(i)')
  BY NotType DEF GBb, BB, W, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GBb(i,"a1") => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME GBb(i,"a1") PROVE ENABLED <<proc(Not(i))>>_vars  OBVIOUS
  <2>0. pc[Not(i)]="a1" /\ TypeOK  BY NotType DEF GBb, InvL
  <2> DEFINE q == [pc EXCEPT ![Not(i)] = "a2"]
  <2>1. q # pc  BY <2>0, NotType DEF TypeOK
  <2> QED BY <2>0, <2>1, NotType, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK, Not
<1>wf. Spec => WF_vars(proc(Not(i)))  BY NotType DEF Spec
<1>4. Spec => (GBb(i,"a1") ~> (BB(i,"a2") \/ CS(i)))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GBb, BB

LEMMA L_Ba0 == ASSUME NEW i \in {0,1}
   PROVE Spec => (BB(i,"a0") ~> (BB(i,"a1") \/ CS(i)))
<1>1. GBb(i,"a0") /\ [Nxt]_vars => (GBb(i,"a0")' \/ (BB(i,"a1")' \/ CS(i)'))
  BY NotType DEF GBb, BB, W, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GBb(i,"a0") /\ <<proc(Not(i))>>_vars => (BB(i,"a1")' \/ CS(i)')
  BY NotType DEF GBb, BB, W, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GBb(i,"a0") => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME GBb(i,"a0") PROVE ENABLED <<proc(Not(i))>>_vars  OBVIOUS
  <2>0. pc[Not(i)]="a0" /\ TypeOK  BY NotType DEF GBb, InvL
  <2> DEFINE q == [pc EXCEPT ![Not(i)] = "a1"]
  <2>1. q # pc  BY <2>0, NotType DEF TypeOK
  <2> QED BY <2>0, <2>1, NotType, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK, Not
<1>wf. Spec => WF_vars(proc(Not(i)))  BY NotType DEF Spec
<1>4. Spec => (GBb(i,"a0") ~> (BB(i,"a1") \/ CS(i)))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GBb, BB

LEMMA L_Ba4 == ASSUME NEW i \in {0,1}
   PROVE Spec => (BB(i,"a4") ~> (BB(i,"a0") \/ CS(i)))
<1>1. GBb(i,"a4") /\ [Nxt]_vars => (GBb(i,"a4")' \/ (BB(i,"a0")' \/ CS(i)'))
  BY NotType DEF GBb, BB, W, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GBb(i,"a4") /\ <<proc(Not(i))>>_vars => (BB(i,"a0")' \/ CS(i)')
  BY NotType DEF GBb, BB, W, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GBb(i,"a4") => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME GBb(i,"a4") PROVE ENABLED <<proc(Not(i))>>_vars  OBVIOUS
  <2>0. pc[Not(i)]="a4" /\ TypeOK  BY NotType DEF GBb, InvL
  <2> DEFINE q == [pc EXCEPT ![Not(i)] = "a0"]
  <2>1. q # pc  BY <2>0, NotType DEF TypeOK
  <2> QED BY <2>0, <2>1, NotType, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK, Not
<1>wf. Spec => WF_vars(proc(Not(i)))  BY NotType DEF Spec
<1>4. Spec => (GBb(i,"a4") ~> (BB(i,"a0") \/ CS(i)))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GBb, BB

LEMMA L_Bcs == ASSUME NEW i \in {0,1}
   PROVE Spec => (BB(i,"cs") ~> (BB(i,"a4") \/ CS(i)))
<1>1. GBb(i,"cs") /\ [Nxt]_vars => (GBb(i,"cs")' \/ (BB(i,"a4")' \/ CS(i)'))
  BY NotType DEF GBb, BB, W, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GBb(i,"cs") /\ <<proc(Not(i))>>_vars => (BB(i,"a4")' \/ CS(i)')
  BY NotType DEF GBb, BB, W, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GBb(i,"cs") => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME GBb(i,"cs") PROVE ENABLED <<proc(Not(i))>>_vars  OBVIOUS
  <2>0. pc[Not(i)]="cs" /\ TypeOK  BY NotType DEF GBb, InvL
  <2> DEFINE q == [pc EXCEPT ![Not(i)] = "a4"]
  <2>1. q # pc  BY <2>0, NotType DEF TypeOK
  <2> QED BY <2>0, <2>1, NotType, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK, Not
<1>wf. Spec => WF_vars(proc(Not(i)))  BY NotType DEF Spec
<1>4. Spec => (GBb(i,"cs") ~> (BB(i,"a4") \/ CS(i)))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GBb, BB

LEMMA L_Ba3b == ASSUME NEW i \in {0,1}
   PROVE Spec => (BB(i,"a3b") ~> (BB(i,"cs") \/ CS(i)))
<1>1. GBb(i,"a3b") /\ [Nxt]_vars => (GBb(i,"a3b")' \/ (BB(i,"cs")' \/ CS(i)'))
  BY NotType DEF GBb, BB, W, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GBb(i,"a3b") /\ <<proc(Not(i))>>_vars => (BB(i,"cs")' \/ CS(i)')
  BY NotType DEF GBb, BB, W, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GBb(i,"a3b") => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME GBb(i,"a3b") PROVE ENABLED <<proc(Not(i))>>_vars  OBVIOUS
  <2>0. pc[Not(i)]="a3b" /\ turn=Not(i) /\ TypeOK  BY NotType DEF GBb, InvL
  <2>1. turn # Not(Not(i))  BY <2>0, NotType
  <2> DEFINE q == [pc EXCEPT ![Not(i)] = "cs"]
  <2>2. q # pc  BY <2>0, NotType DEF TypeOK
  <2> QED BY <2>0, <2>1, <2>2, NotType, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK, Not
<1>wf. Spec => WF_vars(proc(Not(i)))  BY NotType DEF Spec
<1>4. Spec => (GBb(i,"a3b") ~> (BB(i,"cs") \/ CS(i)))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GBb, BB

LEMMA L_Ba3a == ASSUME NEW i \in {0,1}
   PROVE Spec => (BB(i,"a3a") ~> (BB(i,"a3b") \/ CS(i)))
<1>1. GBb(i,"a3a") /\ [Nxt]_vars => (GBb(i,"a3a")' \/ (BB(i,"a3b")' \/ CS(i)'))
  BY NotType DEF GBb, BB, W, Nxt, Next, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>2. GBb(i,"a3a") /\ <<proc(Not(i))>>_vars => (BB(i,"a3b")' \/ CS(i)')
  BY NotType DEF GBb, BB, W, InvL, TypeOK, CS, proc, a0,a1,a2,a3a,a3b,cs,a4, vars, Not
<1>3. GBb(i,"a3a") => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME GBb(i,"a3a") PROVE ENABLED <<proc(Not(i))>>_vars  OBVIOUS
  <2>0. pc[Not(i)]="a3a" /\ TypeOK  BY NotType DEF GBb, InvL
  <2>a. CASE flag[Not(Not(i))]
    <3> DEFINE q == [pc EXCEPT ![Not(i)] = "a3b"]
    <3>1. q # pc  BY <2>0, NotType DEF TypeOK
    <3> QED BY <2>0, <2>a, <3>1, NotType, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK, Not
  <2>b. CASE ~flag[Not(Not(i))]
    <3> DEFINE q == [pc EXCEPT ![Not(i)] = "cs"]
    <3>1. q # pc  BY <2>0, NotType DEF TypeOK
    <3> QED BY <2>0, <2>b, <3>1, NotType, ExpandENABLED DEF proc, a0,a1,a2,a3a,a3b,cs,a4, vars, TypeOK, Not
  <2> QED BY <2>a, <2>b
<1>wf. Spec => WF_vars(proc(Not(i)))  BY NotType DEF Spec
<1>4. Spec => (GBb(i,"a3a") ~> (BB(i,"a3b") \/ CS(i)))
  BY <1>1, <1>2, <1>3, <1>wf, Nxt_Lemma, PTL
<1> QED BY <1>4, InvL_Lemma, PTL DEF GBb, BB

LEMMA C_B == ASSUME NEW i \in {0,1}
   PROVE Spec => ((W(i) /\ turn=Not(i)) ~> ((W(i) /\ turn=i) \/ CS(i)))
<1>a3a. Spec => (BB(i,"a3a") ~> (BB(i,"a3b") \/ CS(i)))  BY L_Ba3a
<1>a3b. Spec => (BB(i,"a3b") ~> (BB(i,"cs") \/ CS(i)))   BY L_Ba3b
<1>cs.  Spec => (BB(i,"cs") ~> (BB(i,"a4") \/ CS(i)))    BY L_Bcs
<1>a4.  Spec => (BB(i,"a4") ~> (BB(i,"a0") \/ CS(i)))    BY L_Ba4
<1>a0.  Spec => (BB(i,"a0") ~> (BB(i,"a1") \/ CS(i)))    BY L_Ba0
<1>a1.  Spec => (BB(i,"a1") ~> (BB(i,"a2") \/ CS(i)))    BY L_Ba1
<1>a2.  Spec => (BB(i,"a2") ~> ((W(i) /\ turn=i) \/ CS(i)))  BY L_Ba2
<1>inv. Spec => []InvL  BY InvL_Lemma
<1>dis. InvL /\ W(i) /\ turn=Not(i) =>
          \/ BB(i,"a3a") \/ BB(i,"a3b") \/ BB(i,"cs") \/ BB(i,"a4")
          \/ BB(i,"a0") \/ BB(i,"a1") \/ BB(i,"a2")
  BY NotType DEF InvL, TypeOK, BB, W
<1> QED
  BY <1>a3a, <1>a3b, <1>cs, <1>a4, <1>a0, <1>a1, <1>a2, <1>inv, <1>dis, PTL

LEMMA C_W == ASSUME NEW i \in {0,1}
   PROVE Spec => (W(i) ~> CS(i))
<1>1. Spec => ((W(i) /\ turn=i) ~> CS(i))  BY C_A
<1>2. Spec => ((W(i) /\ turn=Not(i)) ~> ((W(i) /\ turn=i) \/ CS(i)))  BY C_B
<1>inv. Spec => []InvL  BY InvL_Lemma
<1>dis. InvL /\ W(i) => ((W(i) /\ turn=i) \/ (W(i) /\ turn=Not(i)))
  BY NotType DEF InvL, TypeOK, W
<1> QED BY <1>1, <1>2, <1>inv, <1>dis, PTL

\* ----- from any control point process i reaches its critical section -----

\* Opaque wrapper: lets the final theorem instantiate the temporal conclusion
\* of Live at the concrete processes 0 and 1 by ordinary (first-order)
\* instantiation, after which DEF LiveCS unfolds it for the PTL backend.
LiveCS(k) == TRUE ~> CS(k)

LEMMA Live == ASSUME NEW i \in {0,1}
   PROVE Spec => LiveCS(i)
<1> SUFFICES Spec => (TRUE ~> CS(i))  BY DEF LiveCS
<1>inv. Spec => []InvL  BY InvL_Lemma
<1>a0. Spec => ((pc[i]="a0") ~> (pc[i]="a1"))   BY L_a0
<1>a1. Spec => ((pc[i]="a1") ~> (pc[i]="a2"))   BY L_a1
<1>a2. Spec => ((pc[i]="a2") ~> (pc[i]="a3a"))  BY L_a2
<1>a4. Spec => ((pc[i]="a4") ~> (pc[i]="a0"))   BY L_a4
<1>w.  Spec => (W(i) ~> CS(i))  BY C_W
<1>dis. InvL => (\/ pc[i]="a0" \/ pc[i]="a1" \/ pc[i]="a2" \/ pc[i]="a3a"
                 \/ pc[i]="a3b" \/ pc[i]="cs" \/ pc[i]="a4")
  BY DEF InvL, TypeOK
<1> QED BY <1>inv, <1>a0, <1>a1, <1>a2, <1>a4, <1>w, <1>dis, PTL DEF W, CS

THEOREM FairSpec => Liveness
<1>1. FairSpec => Spec  BY DEF FairSpec
<1>2. Spec => LiveCS(0)  BY Live
<1>3. Spec => LiveCS(1)  BY Live
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Liveness, Wait, LiveCS

=============================================================================
