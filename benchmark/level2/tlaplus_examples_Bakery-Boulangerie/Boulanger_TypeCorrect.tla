------------------------------ MODULE Boulanger_TypeCorrect ----------------------------

EXTENDS Boulanger

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs", "exit"}]
          /\ previous \in [Procs -> Nat \cup {-1}]             

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

=============================================================================

