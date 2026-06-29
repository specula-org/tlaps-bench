------------------------------- MODULE CRDT_proof_OGLiveness ---------------------------------
EXTENDS CRDT_proof

(***************************************************************************)
(* Proofs of safety properties.                                            *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM Safe == Spec => []Safety
PROOF OMITTED

THEOREM Spec => Monotonicity
PROOF OMITTED
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

(***************************************************************************)
(* Definition of the termination measure.                                  *)
(* Distance(o) sums the differences between node o's knowledge of the      *)
(* counters of other nodes and their true values.                          *)
(* Measure sums Distance(o), for all nodes o.                              *)
(* We prove elementary facts about the termination measure and in          *)
(* particular show how the Gossip action interacts with it.                *)
(***************************************************************************)
DistFun(o) == [n \in Node |-> counter[n][n] - counter[o][n]]

Distance(o) == Sum(DistFun(o))

Measure == Sum([o \in Node |-> Distance(o)])

LEMMA MeasureType ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : DistFun(o) \in [Node -> Nat]
         /\ \A o \in Node : Distance(o) \in Nat
         /\ Measure \in Nat
PROOF OMITTED

\* We need a copy of the above theorem where all variables are primed.
\* One could derive this from MeasureType using PTL, but we just copy
\* and paste the proof.
LEMMA MeasureTypePrime ==
  ASSUME TypeOK', Safety'
  PROVE  /\ \A o \in Node : DistFun(o)' \in [Node -> Nat]
         /\ \A o \in Node : Distance(o)' \in Nat
         /\ Measure' \in Nat
PROOF OMITTED

\* The termination measure is zero iff all nodes agree on the 
\* counter values of all nodes.
LEMMA MeasureIsZero ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : Distance(o) = 0 
                 <=> \A n \in Node : counter[o][n] = counter[n][n]
         /\ Measure = 0
            <=> \A v,w,n \in Node : counter[v][n] = counter[w][n]
PROOF OMITTED

\* A Gossip action will never increase the measure.
LEMMA GossipDoesntIncreaseMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         [\E n,o \in Node : Gossip(n,o)]_vars
  PROVE  /\ \A v,w \in Node : DistFun(v)'[w] <= DistFun(v)[w]
         /\ \A v \in Node : Distance(v)' <= Distance(v)
         /\ Measure' <= Measure
PROOF OMITTED

\* A non-stuttering Gossip action decreases the measure.
LEMMA GossipDecreasesMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         <<\E n,o \in Node : Gossip(n,o)>>_vars
  PROVE  Measure' < Measure
PROOF OMITTED

(***************************************************************************)
(* Proof of the convergence property for the specification with fairness.  *)
(***************************************************************************)

\* First prove when <<Gossip(n,o)>>_vars is enabled.

LEMMA EnabledGossip ==
  ASSUME NEW n \in Node, NEW o \in Node, TypeOK
  PROVE  (ENABLED <<Gossip(n,o)>>_vars) <=>
         \E v \in Node : counter[o][v] < counter[n][v]
PROOF OMITTED

(***************************************************************************)
(* We now prove convergence for the tail of the behavior in which only     *)
(* Gossip actions may occur. For convenience, we define a TLA+             *)
(* specification characterizing this eventual behavior.                    *)
(***************************************************************************)

\* The following theorem is central to establishing liveness. 
\* Its proof is quite tedious because of a delicate interplay of 
\* predicate and temporal logic reasoning.
THEOREM OGLiveness == OGSpec => <>(\A n, o \in Node : counter[n] = counter[o])
PROOF OBVIOUS

(***************************************************************************)
(* The main liveness theorem is now obtained as a simple corollary.        *)
(***************************************************************************)

=============================================================================
