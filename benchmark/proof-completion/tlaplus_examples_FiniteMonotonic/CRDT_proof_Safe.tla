------------------------------- MODULE CRDT_proof_Safe ---------------------------------
EXTENDS CRDT_proof

(***************************************************************************)
(* Proofs of safety properties.                                            *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM Safe == Spec => []Safety
PROOF OBVIOUS

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

\* We need a copy of the above theorem where all variables are primed.
\* One could derive this from MeasureType using PTL, but we just copy
\* and paste the proof.

\* The termination measure is zero iff all nodes agree on the 
\* counter values of all nodes.

\* A Gossip action will never increase the measure.

\* A non-stuttering Gossip action decreases the measure.

(***************************************************************************)
(* Proof of the convergence property for the specification with fairness.  *)
(***************************************************************************)

\* First prove when <<Gossip(n,o)>>_vars is enabled.

(***************************************************************************)
(* We now prove convergence for the tail of the behavior in which only     *)
(* Gossip actions may occur. For convenience, we define a TLA+             *)
(* specification characterizing this eventual behavior.                    *)
(***************************************************************************)

\* The following theorem is central to establishing liveness. 
\* Its proof is quite tedious because of a delicate interplay of 
\* predicate and temporal logic reasoning.

(***************************************************************************)
(* The main liveness theorem is now obtained as a simple corollary.        *)
(***************************************************************************)

=============================================================================
