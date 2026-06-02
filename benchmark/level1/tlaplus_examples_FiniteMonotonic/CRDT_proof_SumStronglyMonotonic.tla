---- MODULE CRDT_proof_SumStronglyMonotonic ----
EXTENDS FiniteSets, FunctionTheorems, Functions, Naturals, NaturalsInduction, TLAPS
(* ---- Content from module CRDT ---- *)


CONSTANT Node
ASSUME NodeAssumption == IsFiniteSet(Node)

VARIABLE counter
vars == counter

TypeOK == counter \in [Node -> [Node -> Nat]]

Safety == \A n, o \in Node : counter[n][n] >= counter[o][n]

Monotonic == \A n, o \in Node : counter'[n][o] >= counter[n][o]

Monotonicity == [][Monotonic]_counter

\* Repeatedly, the counters at all nodes are in sync.
Convergence == []<>(\A n, o \in Node : counter[n] = counter[o])

Init == counter = [n \in Node |-> [o \in Node |-> 0]]

Increment(n) == counter' = [counter EXCEPT ![n][n] = @ + 1]

Gossip(n, o) ==
  LET Max(a, b) == IF a > b THEN a ELSE b IN
  counter' = [
    counter EXCEPT ![o] = [
      nodeView \in Node |->
        Max(counter[n][nodeView], counter[o][nodeView])
      ]
    ]

Next ==
  \/ \E n \in Node : Increment(n)
  \/ \E n, o \in Node : Gossip(n, o)

Spec ==
  /\ Init
  /\ [][Next]_counter


-----------------------------------------------------------------------------
(***************************************************************************)
(* Fairness and liveness assumptions.                                      *)
(* We assume that Gossip actions will eventually occur when enabled, and   *)
(* that from some point onwards, only Gossip actions will be performed.    *)
(* In other words, incrementation of counters happens only finitely often. *)
(* Note that the second conjunct is not a standard fairness condition,     *)
(* yet the overall specification is machine closed.                        *)
(***************************************************************************)
Fairness ==
    /\ \A n, o \in Node : WF_vars(Gossip(n,o))
    /\ <>[][\E n, o \in Node : Gossip(n,o)]_vars

FairSpec ==
  /\ Spec
  /\ Fairness



(***************************************************************************)
(* Proofs of safety properties.                                            *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
  PROOF OMITTED

THEOREM Safe == Spec => []Safety
  PROOF OMITTED

THEOREM Spec => Monotonicity
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* Sum the values of a vector of natural numbers. We discharge the four    *)
(* Sum lemmas by reducing them to the corresponding `SumFunction` theorems *)
(* in the community-modules `FunctionTheorems`, via the trivial unfolding  *)
(*   Sum(f) = FoldFunction(+, 0, f)                                        *)
(*          = FoldFunctionOnSet(+, 0, f, DOMAIN f)                         *)
(*          = SumFunctionOnSet(f, DOMAIN f)                                *)
(*          = SumFunction(f).                                              *)
(***************************************************************************)
Sum(f) == FoldFunction(+, 0, f)

LEMMA SumIsSumFunction ==
  ASSUME NEW f
  PROVE  Sum(f) = SumFunction(f)
  PROOF OMITTED

LEMMA SumType ==
  ASSUME NEW f \in [Node -> Nat]
  PROVE  Sum(f) \in Nat
  PROOF OMITTED

LEMMA SumIsZero ==
  ASSUME NEW f \in [Node -> Nat]
  PROVE  Sum(f) = 0 <=> \A x \in Node : f[x] = 0
  PROOF OMITTED

LEMMA SumWeaklyMonotonic ==
  ASSUME NEW f \in [Node -> Nat], NEW g \in [Node -> Nat],
         \A x \in Node : f[x] <= g[x]
  PROVE  Sum(f) <= Sum(g)
  PROOF OMITTED

LEMMA SumStronglyMonotonic ==
  ASSUME NEW f \in [Node -> Nat], NEW g \in [Node -> Nat],
         \A x \in Node : f[x] <= g[x],
         \E x \in Node : f[x] < g[x]
  PROVE  Sum(f) < Sum(g)
PROOF OBVIOUS

=============================================================================
========================================