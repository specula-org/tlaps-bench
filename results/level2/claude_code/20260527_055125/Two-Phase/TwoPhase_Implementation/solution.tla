---------------------- MODULE TwoPhase_Implementation -----------------------

EXTENDS Naturals, TLAPS

CONSTANT XInit(_), XAct(_, _, _)

VARIABLE p, c, x

Init == /\ p = 0
        /\ c = 0
        /\ XInit(x)

ProducerStep == /\ p = c
                /\ XAct(0, x, x')
                /\ p' = (p + 1) % 2
                /\ c' = c

ConsumerStep == /\ p # c
                /\ XAct(1, x, x')
                /\ c' = (c + 1) % 2
                /\ p' = p

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_<<p, c, x>>

vBar == (p + c) % 2

A == INSTANCE Alternate WITH v <- vBar

TypeOK == p \in {0, 1} /\ c \in {0, 1}

LEMMA InitTypeOK == Init => TypeOK
  BY DEF Init, TypeOK

LEMMA NextTypeOK == TypeOK /\ [Next]_<<p, c, x>> => TypeOK'
  BY DEF TypeOK, Next, ProducerStep, ConsumerStep

LEMMA InvariantTypeOK == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY InitTypeOK
  <1>2. TypeOK /\ [Next]_<<p, c, x>> => TypeOK'
    BY NextTypeOK
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

LEMMA InitImp == Init => A!Init
  BY DEF Init, A!Init, vBar

LEMMA NextImp == TypeOK /\ [Next]_<<p, c, x>> => [A!Next]_<<vBar, x>>
  <1> SUFFICES ASSUME TypeOK, [Next]_<<p, c, x>>
               PROVE  [A!Next]_<<vBar, x>>
    OBVIOUS
  <1>1. CASE ProducerStep
    <2>1. p = c
      BY <1>1 DEF ProducerStep
    <2>2. vBar = 0
      BY <2>1, TypeOK DEF vBar, TypeOK
    <2>3. vBar' = 1
      <3>1. p' = (p + 1) % 2 /\ c' = c
        BY <1>1 DEF ProducerStep
      <3>2. (p + 1) % 2 \in {0, 1}
        BY TypeOK DEF TypeOK
      <3>3. (p' + c') % 2 = 1
        BY <3>1, <2>1, TypeOK DEF TypeOK
      <3>4. QED BY <3>3 DEF vBar
    <2>4. XAct(vBar, x, x')
      BY <1>1, <2>2 DEF ProducerStep
    <2>5. A!Next
      BY <2>2, <2>3, <2>4 DEF A!Next
    <2>6. QED BY <2>5
  <1>2. CASE ConsumerStep
    <2>1. p # c
      BY <1>2 DEF ConsumerStep
    <2>2. vBar = 1
      BY <2>1, TypeOK DEF vBar, TypeOK
    <2>3. vBar' = 0
      <3>1. c' = (c + 1) % 2 /\ p' = p
        BY <1>2 DEF ConsumerStep
      <3>2. (p' + c') % 2 = 0
        BY <3>1, <2>1, TypeOK DEF TypeOK
      <3>3. QED BY <3>2 DEF vBar
    <2>4. XAct(vBar, x, x')
      BY <1>2, <2>2 DEF ConsumerStep
    <2>5. A!Next
      BY <2>2, <2>3, <2>4 DEF A!Next
    <2>6. QED BY <2>5
  <1>3. CASE UNCHANGED <<p, c, x>>
    <2>1. vBar' = vBar
      BY <1>3 DEF vBar
    <2>2. x' = x
      BY <1>3
    <2>3. QED BY <2>1, <2>2
  <1>4. QED BY <1>1, <1>2, <1>3 DEF Next

THEOREM Implementation == Spec => A!Spec
  <1>1. Init => A!Init
    BY InitImp
  <1>2. TypeOK /\ [Next]_<<p, c, x>> => [A!Next]_<<vBar, x>>
    BY NextImp
  <1>3. Spec => []TypeOK
    BY InvariantTypeOK
  <1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec, A!Spec
==============================================================
