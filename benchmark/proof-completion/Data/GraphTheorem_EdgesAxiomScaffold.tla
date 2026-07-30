---------------------------- MODULE GraphTheorem_EdgesAxiomScaffold ----------------------------
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

=============================================================================
