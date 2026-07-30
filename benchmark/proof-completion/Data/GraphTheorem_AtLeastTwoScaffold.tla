---------------------------- MODULE GraphTheorem_AtLeastTwoScaffold ----------------------------
EXTENDS Sets, TLAPS

\* CONSTANT Nodes
\* ASSUME NodesFinite == IsFiniteSet(Nodes)

Edges(Nodes) == { {m[1], m[2]} : m \in Nodes \X Nodes }
  (*************************************************************************)
  (* The definition we want is                                             *)
  (*                                                                       *)
  (*    Edges == {{m, n} : m, n \in Nodes}                                 *)
  (*                                                                       *)
  (* However, this construct isn't supported by TLAPS yet.                 *)
  (*************************************************************************)

THEOREM EdgesAxiom == \A Nodes :
                       /\ \A m, n \in Nodes : {m, n} \in Edges(Nodes)
                       /\ \A e \in Edges(Nodes) :
                            \E m, n \in Nodes : e = {m, n}
PROOF OMITTED

THEOREM EdgesFinite == \A Nodes :
                          IsFiniteSet(Nodes) => IsFiniteSet(Edges(Nodes))
PROOF OMITTED

NonLoopEdges(Nodes) == {e \in Edges(Nodes) : Cardinality(e) = 2}
SimpleGraphs(Nodes) == SUBSET NonLoopEdges(Nodes)
Degree(n, G) == Cardinality ({e \in G : n \in e})

=============================================================================
