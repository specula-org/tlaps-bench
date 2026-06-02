---- MODULE CRDT_proof_GossipDecreasesMeasure_1 ----
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
  PROOF OMITTED

DistFun(o) == [n \in Node |-> counter[n][n] - counter[o][n]]

Distance(o) == Sum(DistFun(o))

Measure == Sum([o \in Node |-> Distance(o)])

LEMMA MeasureType ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : DistFun(o) \in [Node -> Nat]
         /\ \A o \in Node : Distance(o) \in Nat
         /\ Measure \in Nat
  PROOF OMITTED

LEMMA MeasureTypePrime ==
  ASSUME TypeOK', Safety'
  PROVE  /\ \A o \in Node : DistFun(o)' \in [Node -> Nat]
         /\ \A o \in Node : Distance(o)' \in Nat
         /\ Measure' \in Nat
  PROOF OMITTED

LEMMA MeasureIsZero ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : Distance(o) = 0 
                 <=> \A n \in Node : counter[o][n] = counter[n][n]
         /\ Measure = 0
            <=> \A v,w,n \in Node : counter[v][n] = counter[w][n]
  PROOF OMITTED

LEMMA GossipDoesntIncreaseMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         [\E n,o \in Node : Gossip(n,o)]_vars
  PROVE  /\ \A v,w \in Node : DistFun(v)'[w] <= DistFun(v)[w]
         /\ \A v \in Node : Distance(v)' <= Distance(v)
         /\ Measure' <= Measure
  PROOF OMITTED

LEMMA GossipDecreasesMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         <<\E n,o \in Node : Gossip(n,o)>>_vars
  PROVE  Measure' < Measure
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof of the convergence property for the specification with fairness.  *)
(***************************************************************************)

\* First prove when <<Gossip(n,o)>>_vars is enabled.

LEMMA EnabledGossip ==
  ASSUME NEW n \in Node, NEW o \in Node, TypeOK
  PROVE  (ENABLED <<Gossip(n,o)>>_vars) <=>
         \E v \in Node : counter[o][v] < counter[n][v]
  PROOF OMITTED

OGSpec ==
  /\ [](TypeOK /\ Safety)
  /\ [][\E n, o \in Node : Gossip(n,o)]_vars
  /\ [](\A n, o \in Node : WF_vars(Gossip(n,o)))

\* The following theorem is central to establishing liveness. 
\* Its proof is quite tedious because of a delicate interplay of 
\* predicate and temporal logic reasoning.
THEOREM OGLiveness == OGSpec => <>(\A n, o \in Node : counter[n] = counter[o])
  PROOF OMITTED

THEOREM FairSpec => Convergence
  PROOF OMITTED

=============================================================================

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof of the convergence property for the specification with fairness.  *)
(***************************************************************************)

\* First prove when <<Gossip(n,o)>>_vars is enabled.

LEMMA EnabledGossip ==
  ASSUME NEW n \in Node, NEW o \in Node, TypeOK
  PROVE  (ENABLED <<Gossip(n,o)>>_vars) <=>
         \E v \in Node : counter[o][v] < counter[n][v]
  PROOF OMITTED

DistFun(o) == [n \in Node |-> counter[n][n] - counter[o][n]]

Distance(o) == Sum(DistFun(o))

Measure == Sum([o \in Node |-> Distance(o)])

LEMMA MeasureType ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : DistFun(o) \in [Node -> Nat]
         /\ \A o \in Node : Distance(o) \in Nat
         /\ Measure \in Nat
  PROOF OMITTED

LEMMA MeasureTypePrime ==
  ASSUME TypeOK', Safety'
  PROVE  /\ \A o \in Node : DistFun(o)' \in [Node -> Nat]
         /\ \A o \in Node : Distance(o)' \in Nat
         /\ Measure' \in Nat
  PROOF OMITTED

LEMMA MeasureIsZero ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : Distance(o) = 0 
                 <=> \A n \in Node : counter[o][n] = counter[n][n]
         /\ Measure = 0
            <=> \A v,w,n \in Node : counter[v][n] = counter[w][n]
  PROOF OMITTED

LEMMA GossipDoesntIncreaseMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         [\E n,o \in Node : Gossip(n,o)]_vars
  PROVE  /\ \A v,w \in Node : DistFun(v)'[w] <= DistFun(v)[w]
         /\ \A v \in Node : Distance(v)' <= Distance(v)
         /\ Measure' <= Measure
  PROOF OMITTED

LEMMA GossipDecreasesMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         <<\E n,o \in Node : Gossip(n,o)>>_vars
  PROVE  Measure' < Measure
PROOF OBVIOUS

========================================