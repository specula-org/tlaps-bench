---- MODULE Allocator_AllocateTypeInvariant ----
EXTENDS Allocator_AllocateTypeInvariantScaffold
THEOREM AllocateTypeInvariant ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Allocate(c,S) => TypeInvariant'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
