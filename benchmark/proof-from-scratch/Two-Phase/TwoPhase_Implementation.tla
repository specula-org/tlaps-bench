---------------------- MODULE TwoPhase_Implementation -----------------------

EXTENDS TwoPhase

vBar == (p + c) % 2

A == INSTANCE Alternate WITH v <- vBar

THEOREM Implementation == Spec => A!Spec
PROOF OBVIOUS
==============================================================

