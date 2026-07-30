---- MODULE Allocator_RequestTypeInvariant ----
EXTENDS Allocator_RequestTypeInvariantScaffold
THEOREM RequestTypeInvariant ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Request(c,S) => TypeInvariant'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
