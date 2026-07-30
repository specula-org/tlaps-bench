---- MODULE Allocator_ReturnTypeInvariant ----
EXTENDS Allocator_ReturnTypeInvariantScaffold
THEOREM ReturnTypeInvariant ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Return(c,S) => TypeInvariant'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
