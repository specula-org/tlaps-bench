------------------------- MODULE Termination_proof -------------------------
EXTENDS Termination, TLAPS

(***************************************************************************)
(* This module contains a proof of the safety properties of the            *)
(* termination detection algorithm that is checked by TLAPS.               *)
(*                                                                         *)
(* We start by proving type correctness.                                   *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY Isa DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>1. CASE daemon
    <3>1. CASE visited # P \/ ~ Consistent(P)
      <4>. PICK p \in P :
              /\ ds' = [t \in P\times P |-> IF t[1] = p THEN s[t] ELSE ds[t]]
              /\ dr' = [t \in P\times P |-> IF t[2] = p THEN r[t] ELSE dr[t]]
              /\ visited' = (visited \union {p})
              /\ UNCHANGED <<terminated, s, r>>
        BY <2>1, <3>1, Zenon DEF daemon
      <4>. QED  BY DEF TypeOK
    <3>2. CASE ~(visited # P \/ ~ Consistent(P))
      BY <2>1, <3>2 DEF daemon, TypeOK
    <3>. QED  BY <3>1, <3>2
  <2>2. ASSUME NEW p \in P,
               process(p)
        PROVE  TypeOK'
    BY <2>2 DEF process, TypeOK
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, TypeOK
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* We prove that Inv1 is an inductive invariant,                           *) 
(* relative to type correctness.                                           *)
(***************************************************************************)
LEMMA Invariant1 == Spec => []Inv1
<1>1. Init => Inv1
  BY DEF Init, Inv1
<1>2. TypeOK /\ TypeOK' /\ Inv1 /\ [Next]_vars => Inv1'
  <2> SUFFICES ASSUME TypeOK, TypeOK',
                      Inv1,
                      [Next]_vars
               PROVE  Inv1'
    OBVIOUS
  <2>. USE DEF TypeOK, Inv1
  <2>1. CASE daemon
    BY <2>1 DEF daemon
  <2>2. ASSUME NEW self \in P,
               process(self)
        PROVE  Inv1'
    <3>1. PICK p \in P \ {self}, Q \in SUBSET (P \ {self}) :
               /\ s[<<p, self>>] - r[<<p, self>>] > 0
               /\ r' = [r EXCEPT ![<<p,self>>] = @ + 1]
               /\ s' = [t \in P \X P |-> IF t[1] = self /\ t[2] \in Q
                                         THEN s[t]+1 ELSE s[t]]
               /\ UNCHANGED << ds, dr, visited, terminated >>
      BY <2>2, Zenon DEF process, NumPending
    <3>2. /\ s[<<p,self>>] > r[<<p,self>>]
          /\ s[<<p,self>>] >= r'[<<p,self>>]
      BY <3>1
    <3>3. ASSUME NEW pp \in P, NEW qq \in P
          PROVE  r'[<<pp,qq>>] <= s[<<pp,qq>>] 
      <4>1. CASE pp = p /\ qq = self
        BY <3>2, <4>1
      <4>2. CASE ~(pp = p /\ qq = self)
        BY <3>1, <4>2
      <4>. QED  BY <4>1, <4>2
    <3>4. ASSUME NEW pp \in P, NEW qq \in P
          PROVE  s[<<pp,qq>>] <= s'[<<pp,qq>>]
      BY <3>1
    <3>5. ASSUME NEW pp \in P, NEW qq \in P
          PROVE  r'[<<pp,qq>>] <= s'[<<pp,qq>>]
      BY <3>3, <3>4
    <3>. QED  BY <3>5
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

(***************************************************************************)
(* Now, prove invariance of Inv2 based on the two previous invariants.     *)
(***************************************************************************)
LEMMA Invariant2 == Spec => []Inv2
<1>1. Init => Inv2
  BY DEF Init, Inv2, Stale
<1>2. TypeOK /\ TypeOK' /\ Inv1 /\ Inv2 /\ [Next]_vars => Inv2'
  <2> SUFFICES ASSUME TypeOK, TypeOK',
                      Inv1,
                      Inv2,
                      [Next]_vars
               PROVE  Inv2'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. CASE daemon
    <3>1. CASE visited # P \/ ~ Consistent(P)
      <4>1. PICK self \in P :
              /\ ds' = [t \in P\times P |-> IF t[1] = self THEN s[t] ELSE ds[t]]
              /\ dr' = [t \in P\times P |-> IF t[2] = self THEN r[t] ELSE dr[t]]
              /\ visited' = (visited \union {self})
              /\ UNCHANGED <<terminated, s, r>>
        BY <2>1, <3>1, Zenon DEF daemon
      <4>2. SUFFICES ASSUME NEW Q \in SUBSET visited', 
                            Consistent(Q)', Stale(Q)'
                     PROVE  \E p \in Q, q \in P \ Q : r'[<<q,p>>] > dr'[<<q,p>>]
        BY Zenon DEF Inv2
      <4>3. CASE self \in Q
        <5>. DEFINE QQ == Q \ {self}
        <5>1. QQ \subseteq visited
          BY <4>1
        <5>a. \A p,q \in QQ : ds'[<<p,q>>] = ds[<<p,q>>] /\ dr'[<<p,q>>] = dr[<<p,q>>]
          BY <4>1
        <5>2. Consistent(QQ) /\ Consistent(QQ)'
          BY <5>a, <4>2, Zenon DEF Consistent
        <5>3. Stale(QQ)
          BY <4>1, <4>2, Zenon DEF Stale
        <5>4. PICK p \in QQ, q \in P \ QQ : r[<<q,p>>] > dr[<<q,p>>]
          BY <5>1, <5>2, <5>3, Zenon DEF Inv2
        <5>5. r'[<<q,p>>] > dr'[<<q,p>>]
          BY <5>4, <4>1
        \* It remains to prove that q # self, hence q \in P \ Q
        <5>6. ASSUME q = self PROVE FALSE
          <6>1. r[<<self,p>>] > dr'[<<self,p>>]
            BY <5>5, <5>6, <4>1
          <6>2. @ = ds'[<<self,p>>]
            BY <4>2, <4>3 DEF Consistent
          <6>3. @ = s[<<self,p>>]
            BY <4>1
          <6>. QED  BY <6>1, <6>2, <6>3 DEF Inv1
        <5>. QED  BY <5>5, <5>6, Zenon
      <4>4. CASE self \notin Q
        <5>1. Q \subseteq visited
          BY <4>1, <4>4
        <5>2. Consistent(Q)
          BY <4>1, <4>2, <4>4, ZenonT(20) DEF Consistent
        <5>3. Stale(Q)
          BY <4>1, <4>2, <4>4, Zenon DEF Stale
        <5>4. PICK p \in Q, q \in P \ Q : r[<<q,p>>] > dr[<<q,p>>]
          BY <5>1, <5>2, <5>3 DEF Inv2
        <5>. QED  BY <5>4, <4>1, <4>4, Zenon
      <4>. QED  BY <4>3, <4>4
    <3>2. CASE ~(visited # P \/ ~ Consistent(P))
      BY <2>1, <3>2, Isa DEF daemon, Inv2, Consistent, Stale
    <3>. QED  BY <3>1, <3>2
  <2>2. ASSUME NEW self \in P,
               process(self)
        PROVE  Inv2'
    <3>1. PICK pp \in P \ {self}, QQ \in SUBSET (P \ {self}) :
               /\ s[<<pp, self>>] - r[<<pp, self>>] > 0
               /\ r' = [r EXCEPT ![<<pp,self>>] = @ + 1]
               /\ s' = [t \in P \X P |-> IF t[1] = self /\ t[2] \in QQ
                                         THEN s[t]+1 ELSE s[t]]
               /\ UNCHANGED << ds, dr, visited, terminated >>
      BY <2>2, Zenon DEF process, NumPending
    <3>2. ASSUME NEW Q \in SUBSET visited, 
                 Consistent(Q)', Stale(Q)'
          PROVE  \E p \in Q, q \in P \ Q : r'[<<q,p>>] > dr'[<<q,p>>]
      <4>1. Consistent(Q)
        BY <3>1, <3>2 DEF Consistent
      <4>2. CASE Stale(Q)
        <5>1. PICK p \in Q, q \in P \ Q : r[<<q,p>>] > dr[<<q,p>>]
          BY <4>1, <4>2, Zenon DEF Inv2
        <5>2. r'[<<q,p>>] >= r[<<q,p>>]
          BY <3>1
        <5>3. r'[<<q,p>>] > dr'[<<q,p>>]
          BY <5>1, <5>2, <3>1
        <5>. QED  BY <5>3, Zenon
      <4>3. CASE ~ Stale(Q)
        <5>1. \A p \in Q, q \in P :
                 /\ r[<<q,p>>] = dr[<<q,p>>]
                 /\ s[<<p,q>>] = ds[<<p,q>>]
          BY <4>3, Zenon DEF Stale
        <5>2. ASSUME NEW p \in Q, NEW q \in Q
              PROVE  r'[<<p,q>>] = r[<<p,q>>]
          <6>1. /\ s[<<p,q>>] = ds[<<p,q>>]
                /\ dr[<<p,q>>] = r[<<p,q>>]
            BY <5>1, Zenon
          <6>2. ds[<<p,q>>] = dr[<<p,q>>]
            BY <4>1 DEF Consistent
          <6>. QED  BY <6>1, <6>2, <3>1
        <5>3. PICK p \in Q, q \in P : 
                   \/ r'[<<q,p>>] # dr'[<<q, p>>]
                   \/ s'[<<p,q>>] # ds'[<<p, q>>]
          BY <3>2, Zenon DEF Stale
        <5>4. p = self
          BY <5>3, <5>1, <3>1
        <5>5. pp \notin Q
          BY <5>4, <5>2, <3>1
        <5>6. r[<<pp, self>>] = dr'[<<pp, self>>]
          BY <5>4, <5>1, <3>1, Zenon
        <5>7. r'[<<pp, self>>] > dr'[<<pp, self>>]
          BY <5>6, <3>1
        <5>. QED  BY <5>7, <5>4, <5>5, Zenon
      <4>. QED  BY <4>2, <4>3, Zenon
    <3>. QED  BY <3>1, <3>2, Isa DEF Inv2
  <2>3. CASE UNCHANGED vars
    BY <2>3, Isa DEF vars, Inv2, Consistent, Stale
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>. QED  BY <1>1, <1>2, TypeCorrect, Invariant1, PTL DEF Spec

(***************************************************************************)
(* Proving that Inv3 is an invariant is easy.                              *)
(***************************************************************************)
LEMMA Invariant3 == Spec => []Inv3
<1>1. Init => Inv3
  BY DEF Init, Inv3
<1>2. TypeOK /\ Inv3 /\ [Next]_vars => Inv3'
  BY Zenon DEF TypeOK, Inv3, Next, daemon, process, vars, Consistent
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

(***************************************************************************)
(* Finally, infer that the algorithm satisfies the safety condition.       *)
(***************************************************************************)
THEOREM Spec => []Safety
<1>. TypeOK /\ Inv2 /\ Inv3 => Safety
  <2>. SUFFICES ASSUME TypeOK, Inv2, Inv3, terminated, 
                       NEW p \in P, NEW q \in P
                PROVE  s[<<p,q>>] - r[<<p,q>>] = 0
    BY Zenon DEF Safety, NumPending
  <2>1. visited = P /\ Consistent(P)
    BY DEF Inv3
  <2>2. ds[<<p,q>>] = dr[<<p,q>>]
    BY <2>1 DEF Consistent
  <2>3. ~ Stale(P)
    BY <2>1, Zenon DEF Inv2
  <2>4. s[<<p,q>>] = ds[<<p,q>>] /\ r[<<p,q>>] = dr[<<p,q>>]
    BY <2>3 DEF Stale
  <2>. QED  BY <2>2, <2>4 DEF TypeOK
<1>. QED  BY TypeCorrect, Invariant2, Invariant3, PTL

=============================================================================
