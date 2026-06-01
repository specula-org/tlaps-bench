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

IndInv == /\ p \in 0..1
          /\ c \in 0..1

LEMMA InitIndInv == Init => IndInv
PROOF
  BY DEF Init, IndInv

LEMMA NextIndInv == IndInv /\ [Next]_<<p, c, x>> => IndInv'
PROOF
  BY SMT DEF IndInv, Next, ProducerStep, ConsumerStep

LEMMA SpecIndInv == Spec => []IndInv
PROOF
  BY InitIndInv, NextIndInv, PTL DEF Spec

LEMMA InitImpliesAInit == Init => A!Init
PROOF
  BY SMT DEF Init, A!Init, vBar

LEMMA ProducerStepImpliesANext == IndInv /\ ProducerStep => A!Next
PROOF
  BY SMT DEF IndInv, ProducerStep, A!Next, vBar

LEMMA ConsumerStepImpliesANext == IndInv /\ ConsumerStep => A!Next
PROOF
  BY SMT DEF IndInv, ConsumerStep, A!Next, vBar

LEMMA NextImpliesANext == IndInv /\ Next => A!Next
PROOF
  BY ProducerStepImpliesANext, ConsumerStepImpliesANext DEF Next

LEMMA StutterImpliesAStutter ==
  <<p, c, x>>' = <<p, c, x>> => <<vBar, x>>' = <<vBar, x>>
PROOF
  BY SMT DEF vBar

LEMMA StepSimulation ==
  IndInv /\ IndInv' /\ [Next]_<<p, c, x>> => [A!Next]_<<vBar, x>>
PROOF
  BY NextImpliesANext, StutterImpliesAStutter

LEMMA SpecImpliesANext == Spec => [][A!Next]_<<vBar, x>>
PROOF
  BY SpecIndInv, StepSimulation, PTL DEF Spec

THEOREM Implementation == Spec => A!Spec
PROOF
  BY InitImpliesAInit, SpecImpliesANext DEF Spec, A!Spec
==============================================================
