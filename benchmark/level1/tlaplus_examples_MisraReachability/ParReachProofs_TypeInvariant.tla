---- MODULE ParReachProofs_TypeInvariant ----
EXTENDS FiniteSets, Integers, Sequences, TLAPS
(* ---- Content from module Reachability ---- *)
(***************************************************************************)
(* This module defines reachability in a directed graph.  A directed graph *)
(* is a collection of nodes and directed edges between nodes.  The set of  *)
(* nodes reachable from a node n consists of n and all nodes that can be   *)
(* reached from n by following edges in the direction the edges point.     *)
(* The first thing we must do is decide how to represent a directed graph  *)
(* mathematically.  There are two simple ways to do it.  The most obvious  *)
(* way is by a set Nodes of nodes and a set Edges of edges, where an edge  *)
(* pointing from node n to node m is represented by the pair <<n, m>>.  We *)
(* could do this by declaring Nodes and Edges to be constants and adding   *)
(* the assumption                                                          *)
(*                                                                         *)
(*    ASSUME Edges \subseteq Nodes \X Nodes                                *)
(*                                                                         *)
(* The second way is by a set Nodes of nodes and a function Succ such that *)
(* Succ[n] is the set of nodes pointed to by edges from n.  These two ways *)
(* of representing directed graphs are obviously equivalent.  Starting     *)
(* with Nodes and Edges, we can define Succ by                             *)
(*                                                                         *)
(*    Succ[n \in Nodes] ==                                                 *)
(*       LET EdgesFromN == {e \in Edges : e[1] = n}                        *)
(*       IN  {e[2] : e \in EdgesFromN}                                     *)
(*                                                                         *)
(* Conversely, given Nodes and Succ, we can define Edges by                *)
(*                                                                         *)
(*    Edges == UNION {Succ[n] : n \in Nodes}                               *)
(*                                                                         *)
(* We represent a directed graph by Nodes and Succ.                        *)
(***************************************************************************)

CONSTANTS Nodes,  Succ
ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]


(***************************************************************************)
(* We define ReachableFrom so that for any set S of nodes,                 *)
(* ReachableFrom(S) is the set of nodes reachable from nodes in S--that    *)
(* is, the set of nodes to which there exists a path starting from a node  *)
(* in S.  A path is a sequence of nodes such that there is an edge from    *)
(* each node to the next.  We define ReachableFrom in terms of ExistsPath, *)
(* where ExistsPath(m, n) is true for nodes m and n iff there is a path    *)
(* from m to n.                                                            *)
(***************************************************************************)
IsPathFromTo(p, m, n) == 
       /\ Len(p) > 0
       /\ (p[1] = m) /\ (p[Len(p)] = n)  
       /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]]   

ExistsPath(m, n) == 
   \E p \in Seq(Nodes) : IsPathFromTo(p, m, n)
                      
ReachableFrom(S) == 
   {n \in Nodes : \E m \in S : ExistsPath(m, n)}
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following two statements import modules that are distributed with   *)
(* the TLAPS proof system.  If you get a parsing error because those       *)
(* modules can't be found, then you probably don't have TLAPS installed    *)
(* and should uncomment the following module-ending line so the rest of    *)
(* this module will be ignored.                                            *)
(***************************************************************************)

(* ---- Content from module ParReach ---- *)
(***************************************************************************)
(* This module describes an algorithm that is a multiprocess               *)
(* implementation of the algorithm in module Reachable.  You should        *)
(* understand that algorithm before reading further in this module.        *)
(*                                                                         *)
(* Here, this module's algorithm will be called the parallel algorithm and *)
(* module Reachable's algorithm will be called Misra's algorithm.  The     *)
(* parallel algorithm computes the same thing as Misra's algorithm --      *)
(* namely, it terminates if and only if the set of nodes reachable from    *)
(* Root is finite, in which case the variable `marked' equals that         *)
(* reachable set when the algorithm terminates.  The parallel algorithm    *)
(* does this by implementing Misra's algorithm under a refinement mapping  *)
(* such that                                                               *)
(*                                                                         *)
(*   - The parallel algorithm's `marked' variable implements the Misra     *)
(*     algorithm's variable of the same name.                              *)
(*                                                                         *)
(*   - The parallel algorithm has terminated if and only if Misra's        *)
(*     algorithm has.                                                      *)
(***************************************************************************)

(***************************************************************************)
(* The Misra algorithm's constants Nodes and Succ are imported from module *)
(* Reachability.  Its Root constant is declared here, as is the set Procs  *)
(* of processes that execute the parallel algorithm.                       *)
(***************************************************************************)
CONSTANT Root, Procs

ASSUME RootAssump == Root \in Nodes
ASSUME ProcsAssump == /\ Procs # {}
                      /\ IsFiniteSet(Procs)

Reachable == ReachableFrom({Root})
  (*************************************************************************)
  (* This definition is copied from module Reachable.  (We don't want to   *)
  (* extend that module because it would lead to name conflicts with the   *)
  (* TLA+ translation of the algorithm in this module.)                    *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(****************************************************************************
The algorithm executed by each process is the same as Misra's
algorithm, except that where the Misra algorithm adds to `marked' a
node v in vroot and adds the nodes in Succ[v] to vroot in a single
step, the parallel algorithm first adds v to `marked' and then adds the
nodes in Succ[v] one at a time to vroot in separate steps.

Note that one process can add node v to `marked', and then another
process can remove v from vroot before the first process has added any
nodes in Succ[v] to vroot.  This implies that a process can find vroot
equal to {} and terminate before `marked' contains all the nodes
reachable from Root.  This doesn't affect correctness of the parallel
algorithm because, as long as `marked' doesn't contain all the nodes it
should, there will be at least one process that hasn't terminated.
However, it can cause inefficiency because processes can terminate
while there is still useful work for them to do.  In practice, the
evaluation of the test vroot /= {} can be implemented in a way that
makes it impossible or perhaps very unlikely to obtain the value FALSE
if there are still nodes being added to vroot.  Devising such an
implementation is a nice exercise that will not be discussed here.

Here is the algorithm's PlusCal code.  The initial values of the
process-local variables u and toVroot don't matter.  It's always a good
idea to make them "type correct", and the initial value of toVroot is
an obvious choice that also makes the refinement mapping a little
simpler.
 

--algorithm ParallelReachability {
  variables marked = {}, vroot = {Root};
  fair process (p \in Procs) 
    variables u = Root, toVroot = {} ;
    { a: while (vroot /= {}) 
       {    with (v \in vroot) { u := v };
         b: if (u \notin marked)
              {    marked := marked \cup {u};
                   toVroot := Succ[u] ;
                c: while (toVroot /= {})
                     { with (w \in toVroot) {
                         vroot := vroot \cup {w} ;
                         toVroot := toVroot \ {w} }
                     }
               }
             else { vroot := vroot \ {u} }     
       }
    }
}



***************************************************************************)
\* BEGIN TRANSLATION   Here is the TLA+ translation of the PlusCal code.
VARIABLES marked, vroot, pc, u, toVroot

vars == << marked, vroot, pc, u, toVroot >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ marked = {}
        /\ vroot = {Root}
        (* Process p *)
        /\ u = [self \in Procs |-> Root]
        /\ toVroot = [self \in Procs |-> {}]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ IF vroot /= {}
                 THEN /\ \E v \in vroot:
                           u' = [u EXCEPT ![self] = v]
                      /\ pc' = [pc EXCEPT ![self] = "b"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ u' = u
           /\ UNCHANGED << marked, vroot, toVroot >>

b(self) == /\ pc[self] = "b"
           /\ IF u[self] \notin marked
                 THEN /\ marked' = (marked \cup {u[self]})
                      /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "c"]
                      /\ vroot' = vroot
                 ELSE /\ vroot' = vroot \ {u[self]}
                      /\ pc' = [pc EXCEPT ![self] = "a"]
                      /\ UNCHANGED << marked, toVroot >>
           /\ u' = u

c(self) == /\ pc[self] = "c"
           /\ IF toVroot[self] /= {}
                 THEN /\ \E w \in toVroot[self]:
                           /\ vroot' = (vroot \cup {w})
                           /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                      /\ pc' = [pc EXCEPT ![self] = "c"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                      /\ UNCHANGED << vroot, toVroot >>
           /\ UNCHANGED << marked, u >>

p(self) == a(self) \/ b(self) \/ c(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* The formula Inv defined below is the inductive invariant needed to      *)
(* prove that the parallel algorithm implements the safety part of Misra's *)
(* algorithm.  In addition to type correctness, it asserts two simple      *)
(* relations between the values of the local variables u and toVroot and   *)
(* the control state of the process:                                       *)
(*                                                                         *)
(*  - toVroot = {} except when control is at c                             *)
(*                                                                         *)
(*  - u is in vroot \cup marked when control is at b.  This is invariant   *)
(*    because u is an element of vroot when control arrives at b, and      *)
(*    an element is removed from vroot only after it is added to `marked'. *)
(*                                                                         *)
(* The fact that such a simple invariant is needed to prove that each step *)
(* of the parallel algorithm implements a step allowed by Misra's          *)
(* algorithm means that the easiest way to show that the parallel          *)
(* algorithm is correct, given the correctness of Misra's algorithm, is to *)
(* show that it implements Misra's algorithm.                              *)
(***************************************************************************)
Inv == /\ marked \in SUBSET Nodes
       /\ vroot \in SUBSET Nodes
       /\ u \in [Procs -> Nodes]
       /\ toVroot \in [Procs -> SUBSET Nodes]
       /\ pc \in [Procs -> {"a", "b", "c", "Done"}]
       /\ \A q \in Procs : /\ (pc[q] \in {"a", "b", "Done"}) => (toVroot[q] = {})
                           /\ (pc[q] = "b") => (u[q] \in vroot \cup marked)
                           
(***************************************************************************)
(* To define a refinement mapping from states of the parallel algorithm to *)
(* states of Misra's algorithm, we must define the expressions in this     *)
(* module that represent the values of the Misra algorithm's variables.    *)
(* The value of the variable `marked' of Misra's algorithm is represented  *)
(* by the value of variable `marked' of the parallel algorithm.  The       *)
(* values of the variables vroot and pc of Misra's algorithm are           *)
(* represented by the expressions vrootBar and pcBar defined below.        *)
(*                                                                         *)
(* For the parallel algorithm to implement Misra's algorithm under this    *)
(* refinement mapping, the same b step that adds node u to `marked' must   *)
(* also add Succ[u] to vrootBar.  The c steps that move individual         *)
(* elements of Succ[u] from toVroot must leave vrootBar unchanged.  (Those *)
(* steps implement stuttering steps of Misra's algorithm.) This leads us   *)
(* to the following definition of vrootBar.                                *)
(***************************************************************************) 
vrootBar == vroot \cup UNION {toVroot[i] : i \in Procs}

(***************************************************************************)
(* Since the variable pc of Misra's algorithm always equals "a" or "Done", *)
(* and we want it to equal "Done" if and only if the parallel algorithm    *)
(* has terminated, the definition of pcBar is obvious.                     *)
(***************************************************************************)
pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

R == INSTANCE Reachable WITH vroot <- vrootBar, pc <- pcBar
  (*************************************************************************)
  (* For every definition Op in module Reachable, this statement defines   *)
  (* the operator R!Op in the current module to have as its definition the *)
  (* expression obtained from the definition of Op in module Reachable by  *)
  (* substituting vrootBar for vroot and pcBar for pc.                     *)
  (*************************************************************************)

(***************************************************************************)
(* The following theorem is the TLA+ assertion of the statement that the   *)
(* parallel algorithm implements Misra's algorithm under the refinement    *)
(* mapping defined above.  It can be checked by TLC for models large       *)
(* enough to make us reasonably confident that it is correct.  (To check   *)
(* it, use models with behavior specification spec that check the temporal *)
(* property R!Spec.)                                                       *)
(***************************************************************************)
Refines == R!Spec
THEOREM Spec => Refines

(***************************************************************************)
(* By the definition of formula Spec of module Reachable, this theorem     *)
(* follows from the following two theorems, the first showing that the     *)
(* parallel algorithm implements the safety part of Misra's algorithm      *)
(* (which implies partial correctness) and the second showing that it      *)
(* implements the fairness part of that algorithm (which implies           *)
(* termination).  Module ParReachProofs contains a TLAPS checked proof of  *)
(* the first theorem.                                                      *)
(***************************************************************************)
THEOREM Spec => R!Init /\ [][R!Next]_R!vars
THEOREM Spec => WF_R!vars(R!Next)

(***************************************************************************)
(* This module contains TLAPS checked proofs of the safety properties      *)
(* asserted in module ParReach--namely, the invariance of Inv and that the *)
(* parallel algorithm implements the safety part of Misra's algorithm under *)
(* the refinement mapping defined there.                                   *)
(***************************************************************************)

LEMMA TypeInvariant == Spec  => []Inv
PROOF OBVIOUS

========================================