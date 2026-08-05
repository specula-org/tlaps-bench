------------ MODULE Bakery_TypeCorrectDefs ----------------------------

EXTENDS BakeryModel

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs", "exit"}]             

=============================================================================

Test 1:  5248 distinct initial states  151056 full initial states
IInit == TypeOK /\ IInv 
