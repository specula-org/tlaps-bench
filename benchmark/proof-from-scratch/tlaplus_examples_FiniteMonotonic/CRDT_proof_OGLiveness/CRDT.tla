------------------------------- MODULE CRDT ---------------------------------

EXTENDS Naturals, FiniteSets

CONSTANT Node
ASSUME NodeAssumption == IsFiniteSet(Node)

VARIABLE counter
vars == counter

TypeOK == counter \in [Node -> [Node -> Nat]]

Safety == \A n, o \in Node : counter[n][n] >= counter[o][n]

Gossip(n, o) ==
  LET Max(a, b) == IF a > b THEN a ELSE b IN
  counter' = [
    counter EXCEPT ![o] = [
      nodeView \in Node |->
        Max(counter[n][nodeView], counter[o][nodeView])
      ]
    ]

-----------------------------------------------------------------------------

=============================================================================

