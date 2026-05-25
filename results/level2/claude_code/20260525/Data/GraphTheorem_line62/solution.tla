---------------------------- MODULE GraphTheorem_line62 ----------------------------
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


-------------------------------------------------------

NonLoopEdges(Nodes) == {e \in Edges(Nodes) : Cardinality(e) = 2}
SimpleGraphs(Nodes) == SUBSET NonLoopEdges(Nodes)
Degree(n, G) == Cardinality ({e \in G : n \in e})


------------------------------------------------------------------
(***************************************************************************)
(* Here's an informal proof of the following theorem                       *)
(*                                                                         *)
(* THEOREM For any finite graph G with no self loops and with more than 1  *)
(* node, there exist two nodes with the same degree.                       *)
(*                                                                         *)
(* <1>1. It suffices to assume G has at most one node with degree 0.       *)
(*   PROOF The theorem is obviously true if G has two nodes with degree 0. *)
(* <1>2. Let H be the subgraph of G obtained by eliminating all            *)
(*       nodes of degree 0.                                                *)
(* <1>3. H as at least 1 node.                                             *)
(*   PROOF By <1>1 and the assumption that G has                           *)
(*       more than one node.                                               *)
(* <1>4. The degree of every node in H is greater than 1 and less than     *)
(*       Cardinality(H).                                                   *)
(*   <2>1. For any node n of H, Degree(n, H) > 0                           *)
(*     PROOF by definition of H.                                           *)
(*         Degree(n, H) < Cardinality                                      *)
(*                                                                         *)
(* <1>5. QED                                                               *)
(*   BY <1>4 and the pigeonhole principle                                  *)
(*                                                                         *)
(* The formal proof doesn't follow exactly this structure.                 *)
(***************************************************************************)
-------------------------------------------------------
(***************************************************************************)
(* Scaffolding definitions and lemmas for the proof.                       *)
(***************************************************************************)

\* Incident edges of node n in graph GG.  Note Degree(n, GG) = Cardinality(Inc(n, GG)).
Inc(n, GG) == {e \in GG : n \in e}

\* The "other" endpoint of an edge e relative to node n.
Other(n, e) == CHOOSE x \in e : x # n

\* Neighbors of node n in graph GG.
Nbr(Nds, n, GG) == {x \in Nds : x # n /\ {n, x} \in GG}

\* Map sending each incident edge to its other endpoint; a bijection Inc -> Nbr.
TheBij(Nds, n, GG) == [e \in Inc(n, GG) |-> Other(n, e)]

-------------------------------------------------------
(* Every non-loop edge is a two-element subset {a,b} of the node set. *)
LEMMA EdgeForm ==
  ASSUME NEW Nds, NEW e \in NonLoopEdges(Nds)
  PROVE  \E a, b : a \in Nds /\ b \in Nds /\ a # b /\ e = {a, b}
PROOF
  <1>1. e \in Edges(Nds) /\ Cardinality(e) = 2
    BY DEF NonLoopEdges
  <1>2. \E m \in Nds \X Nds : e = {m[1], m[2]}
    BY <1>1 DEF Edges
  <1>3. PICK m \in Nds \X Nds : e = {m[1], m[2]}
    BY <1>2
  <1>4. m[1] \in Nds /\ m[2] \in Nds
    BY <1>3
  <1>5. m[1] # m[2]
    <2>1. SUFFICES ASSUME m[1] = m[2] PROVE FALSE
      OBVIOUS
    <2>2. e = {m[1]}
      BY <1>3, <2>1
    <2>3. Cardinality(e) = 1
      BY <2>2, CardinalityOne
    <2>4. QED
      BY <1>1, <2>3
  <1>6. QED
    BY <1>3, <1>4, <1>5

-------------------------------------------------------
(* The set of edges of a finite node set is finite. *)
LEMMA EdgesFinite ==
  ASSUME NEW Nds, IsFiniteSet(Nds)
  PROVE  IsFiniteSet(Edges(Nds)) /\ IsFiniteSet(NonLoopEdges(Nds))
PROOF
  <1>1. Edges(Nds) \subseteq SUBSET Nds
    <2>1. ASSUME NEW e \in Edges(Nds) PROVE e \in SUBSET Nds
      <3>1. PICK m \in Nds \X Nds : e = {m[1], m[2]}
        BY <2>1 DEF Edges
      <3>2. m[1] \in Nds /\ m[2] \in Nds
        BY <3>1
      <3>3. e \subseteq Nds
        BY <3>1, <3>2
      <3>4. QED
        BY <3>3
    <2>2. QED
      BY <2>1
  <1>2. IsFiniteSet(SUBSET Nds)
    BY SubsetsFinite
  <1>3. IsFiniteSet(Edges(Nds))
    BY <1>1, <1>2, FiniteSubset
  <1>4. NonLoopEdges(Nds) \subseteq Edges(Nds)
    BY DEF NonLoopEdges
  <1>5. QED
    BY <1>3, <1>4, FiniteSubset

-------------------------------------------------------
(* Properties of the "other endpoint" of a non-loop edge containing n. *)
LEMMA OtherProps ==
  ASSUME NEW Nds, NEW e \in NonLoopEdges(Nds), NEW n, n \in e
  PROVE  /\ Other(n, e) \in Nds
         /\ Other(n, e) # n
         /\ e = {n, Other(n, e)}
PROOF
  <1>1. PICK a, b : a \in Nds /\ b \in Nds /\ a # b /\ e = {a, b}
    BY EdgeForm
  <1>2. \E x \in e : x # n
    BY <1>1
  <1>3. Other(n, e) \in e /\ Other(n, e) # n
    BY <1>2 DEF Other
  <1>4. Other(n, e) \in Nds
    BY <1>1, <1>3
  <1>5. e = {n, Other(n, e)}
    BY <1>1, <1>3
  <1>6. QED
    BY <1>3, <1>4, <1>5

-------------------------------------------------------
(* Degree of n equals the number of neighbors of n; both finite. *)
LEMMA DegreeNbr ==
  ASSUME NEW Nds, IsFiniteSet(Nds),
         NEW GG \in SimpleGraphs(Nds), NEW n \in Nds
  PROVE  /\ IsFiniteSet(Inc(n, GG))
         /\ IsFiniteSet(Nbr(Nds, n, GG))
         /\ Cardinality(Inc(n, GG)) = Cardinality(Nbr(Nds, n, GG))
PROOF
  <1> DEFINE I == Inc(n, GG)
  <1> DEFINE Nb == Nbr(Nds, n, GG)
  <1> DEFINE f == TheBij(Nds, n, GG)
  <1>g. GG \subseteq NonLoopEdges(Nds)
    BY DEF SimpleGraphs
  <1>e. ASSUME NEW e \in I PROVE e \in NonLoopEdges(Nds) /\ n \in e /\ e \in GG
    BY <1>g DEF Inc
  <1>fin1. IsFiniteSet(I)
    <2>1. I \subseteq NonLoopEdges(Nds)
      BY <1>g DEF Inc
    <2>2. IsFiniteSet(NonLoopEdges(Nds))
      BY EdgesFinite
    <2>3. QED
      BY <2>1, <2>2, FiniteSubset
  <1>fin2. IsFiniteSet(Nb)
    <2>1. Nb \subseteq Nds
      BY DEF Nbr
    <2>2. QED
      BY <2>1, FiniteSubset
  <1>b1. f \in [I -> Nb]
    <2>1. ASSUME NEW e \in I PROVE f[e] \in Nb
      <3>1. e \in NonLoopEdges(Nds) /\ n \in e /\ e \in GG
        BY <1>e
      <3>2. Other(n, e) \in Nds /\ Other(n, e) # n /\ e = {n, Other(n, e)}
        BY <3>1, OtherProps
      <3>3. {n, Other(n, e)} \in GG
        BY <3>1, <3>2
      <3>4. f[e] = Other(n, e)
        BY DEF TheBij
      <3>5. QED
        BY <3>2, <3>3, <3>4 DEF Nbr
    <2>2. QED
      BY <2>1 DEF TheBij
  <1>b2. \A x, y \in I : x # y => f[x] # f[y]
    <2>1. ASSUME NEW x \in I, NEW y \in I, f[x] = f[y] PROVE x = y
      <3>1. x \in NonLoopEdges(Nds) /\ n \in x
        BY <1>e
      <3>2. y \in NonLoopEdges(Nds) /\ n \in y
        BY <1>e
      <3>3. x = {n, Other(n, x)}
        BY <3>1, OtherProps
      <3>4. y = {n, Other(n, y)}
        BY <3>2, OtherProps
      <3>5. Other(n, x) = Other(n, y)
        BY <2>1 DEF TheBij
      <3>6. QED
        BY <3>3, <3>4, <3>5
    <2>2. QED
      BY <2>1
  <1>b3. \A y \in Nb : \E e \in I : f[e] = y
    <2>1. ASSUME NEW y \in Nb PROVE \E e \in I : f[e] = y
      <3>1. y \in Nds /\ y # n /\ {n, y} \in GG
        BY DEF Nbr
      <3>2. {n, y} \in NonLoopEdges(Nds)
        BY <3>1, <1>g
      <3>3. {n, y} \in I
        BY <3>1 DEF Inc
      <3>4. n \in {n, y}
        OBVIOUS
      <3>5. Other(n, {n, y}) \in {n, y} /\ Other(n, {n, y}) # n
        BY <3>2, <3>4, OtherProps
      <3>6. Other(n, {n, y}) = y
        BY <3>1, <3>5
      <3>7. f[{n, y}] = y
        BY <3>3, <3>6 DEF TheBij
      <3>8. QED
        BY <3>3, <3>7
    <2>2. QED
      BY <2>1
  <1>bij. IsBijection(f, I, Nb)
    BY <1>b1, <1>b2, <1>b3 DEF IsBijection
  <1>card. Cardinality(I) = Cardinality(Nb)
    BY <1>bij, <1>fin1, <1>fin2, IsBijectionCardinality
  <1>qed. QED
    BY <1>fin1, <1>fin2, <1>card

-------------------------------------------------------
(* A subset of a finite set with equal cardinality is the whole set. *)
LEMMA SubsetEqCard ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT,
         Cardinality(S) = Cardinality(TT)
  PROVE  S = TT
PROOF
  <1>1. SUFFICES ASSUME S # TT PROVE FALSE
    OBVIOUS
  <1>2. PICK y \in TT : y \notin S
    BY <1>1
  <1>3. S \subseteq (TT \ {y})
    BY <1>2
  <1>4. IsFiniteSet(TT \ {y}) /\ Cardinality(TT \ {y}) = Cardinality(TT) - 1
    BY <1>2, CardinalitySetMinus
  <1>5. Cardinality(S) =< Cardinality(TT \ {y})
    BY <1>3, <1>4, FiniteSubset
  <1>6. Cardinality(TT) \in Nat
    BY CardinalityInNat
  <1>7. QED
    BY <1>4, <1>5, <1>6

-------------------------------------------------------
(* If some node has degree N-1, then every node has positive degree. *)
LEMMA MaxDegree ==
  ASSUME NEW Nds, IsFiniteSet(Nds), Cardinality(Nds) > 1,
         NEW GG \in SimpleGraphs(Nds),
         NEW n \in Nds, Degree(n, GG) = Cardinality(Nds) - 1,
         NEW x \in Nds
  PROVE  Degree(x, GG) > 0
PROOF
  <1> DEFINE Nb == Nbr(Nds, n, GG)
  <1>nat. Cardinality(Nds) \in Nat /\ Cardinality(Nds) >= 2
    BY CardinalityInNat
  <1>1. /\ IsFiniteSet(Inc(n, GG))
        /\ IsFiniteSet(Nb)
        /\ Cardinality(Inc(n, GG)) = Cardinality(Nb)
    BY DegreeNbr
  <1>2. Degree(n, GG) = Cardinality(Nb)
    BY <1>1 DEF Degree, Inc
  <1>3. Cardinality(Nb) = Cardinality(Nds) - 1
    BY <1>2
  <1>4. Nb \subseteq (Nds \ {n})
    BY DEF Nbr
  <1>5. IsFiniteSet(Nds \ {n}) /\ Cardinality(Nds \ {n}) = Cardinality(Nds) - 1
    BY CardinalitySetMinus
  <1>6. Cardinality(Nb) = Cardinality(Nds \ {n})
    BY <1>3, <1>5
  <1>7. Nb = Nds \ {n}
    BY <1>4, <1>5, <1>6, SubsetEqCard
  <1>8. CASE x = n
    BY <1>8, <1>nat
  <1>9. CASE x # n
    <2>1. x \in Nds \ {n}
      BY <1>9
    <2>2. x \in Nb
      BY <2>1, <1>7
    <2>3. {n, x} \in GG
      BY <2>2 DEF Nbr
    <2>4. {n, x} \in Inc(x, GG)
      BY <2>3 DEF Inc
    <2>5. Inc(x, GG) # {}
      BY <2>4
    <2>6. IsFiniteSet(Inc(x, GG))
      BY DegreeNbr
    <2>7. Cardinality(Inc(x, GG)) \in Nat
      BY <2>6, CardinalityInNat
    <2>8. Cardinality(Inc(x, GG)) # 0
      BY <2>5, <2>6, CardinalityZero
    <2>9. QED
      BY <2>7, <2>8 DEF Degree, Inc
  <1>10. QED
    BY <1>8, <1>9

-------------------------------------------------------
(* Every degree is a natural number bounded by N-1. *)
LEMMA DegreeBound ==
  ASSUME NEW Nds, IsFiniteSet(Nds),
         NEW GG \in SimpleGraphs(Nds), NEW n \in Nds
  PROVE  /\ Degree(n, GG) \in Nat
         /\ Degree(n, GG) =< Cardinality(Nds) - 1
PROOF
  <1> DEFINE Nb == Nbr(Nds, n, GG)
  <1>1. /\ IsFiniteSet(Inc(n, GG))
        /\ IsFiniteSet(Nb)
        /\ Cardinality(Inc(n, GG)) = Cardinality(Nb)
    BY DegreeNbr
  <1>2. Degree(n, GG) = Cardinality(Nb)
    BY <1>1 DEF Degree, Inc
  <1>3. Degree(n, GG) \in Nat
    <2>1. Cardinality(Inc(n, GG)) \in Nat
      BY <1>1, CardinalityInNat
    <2>2. QED
      BY <2>1 DEF Degree, Inc
  <1>4. Nb \subseteq (Nds \ {n})
    BY DEF Nbr
  <1>5. IsFiniteSet(Nds \ {n}) /\ Cardinality(Nds \ {n}) = Cardinality(Nds) - 1
    BY CardinalitySetMinus
  <1>6. Cardinality(Nb) =< Cardinality(Nds \ {n})
    BY <1>4, <1>5, FiniteSubset
  <1>7. QED
    BY <1>2, <1>3, <1>5, <1>6

-------------------------------------------------------
THEOREM
  ASSUME NEW Nodes, IsFiniteSet(Nodes), Cardinality(Nodes) > 1,
         NEW G \in SimpleGraphs(Nodes)
  PROVE  \E m, n \in Nodes : /\ m # n
                             /\ Degree(m, G) = Degree(n, G)
PROOF
  <1> DEFINE N == Cardinality(Nodes)
  <1> DEFINE HasMax == \E nn \in Nodes : Degree(nn, G) = N - 1
  <1> DEFINE T == IF HasMax THEN 1..(N-1) ELSE 0..(N-2)
  <1> DEFINE f == [nd \in Nodes |-> Degree(nd, G)]
  <1>nat. N \in Nat /\ N >= 2
    BY CardinalityInNat
  <1>f. f \in [Nodes -> T]
    <2>1. ASSUME NEW nd \in Nodes PROVE f[nd] \in T
      <3>1. Degree(nd, G) \in Nat /\ Degree(nd, G) =< N - 1
        BY DegreeBound
      <3>2. f[nd] = Degree(nd, G)
        OBVIOUS
      <3>3. CASE HasMax
        <4>1. PICK nn \in Nodes : Degree(nn, G) = N - 1
          BY <3>3
        <4>2. Degree(nd, G) > 0
          BY <4>1, MaxDegree
        <4>3. Degree(nd, G) \in 1..(N-1)
          BY <3>1, <4>2, <1>nat
        <4>4. T = 1..(N-1)
          BY <3>3
        <4>5. QED
          BY <3>2, <4>3, <4>4
      <3>4. CASE ~HasMax
        <4>1. Degree(nd, G) # N - 1
          BY <3>4
        <4>2. Degree(nd, G) \in 0..(N-2)
          BY <3>1, <4>1, <1>nat
        <4>3. T = 0..(N-2)
          BY <3>4
        <4>4. QED
          BY <3>2, <4>2, <4>3
      <3>5. QED
        BY <3>3, <3>4
    <2>2. QED
      BY <2>1
  <1>t. IsFiniteSet(T) /\ Cardinality(T) = N - 1
    <2>1. CASE HasMax
      <3>1. T = 1..(N-1)
        BY <2>1
      <3>2. (1 \in Nat) /\ (N - 1 \in Nat)
        BY <1>nat
      <3>3. /\ IsFiniteSet(1..(N-1))
            /\ Cardinality(1..(N-1)) = IF 1 > N-1 THEN 0 ELSE (N-1)-1+1
        BY <3>2, IntervalCardinality
      <3>4. ~(1 > N - 1)
        BY <1>nat
      <3>5. QED
        BY <3>1, <3>3, <3>4, <1>nat
    <2>2. CASE ~HasMax
      <3>1. T = 0..(N-2)
        BY <2>2
      <3>2. (0 \in Nat) /\ (N - 2 \in Nat)
        BY <1>nat
      <3>3. /\ IsFiniteSet(0..(N-2))
            /\ Cardinality(0..(N-2)) = IF 0 > N-2 THEN 0 ELSE (N-2)-0+1
        BY <3>2, IntervalCardinality
      <3>4. ~(0 > N - 2)
        BY <1>nat
      <3>5. QED
        BY <3>1, <3>3, <3>4, <1>nat
    <2>3. QED
      BY <2>1, <2>2
  <1>lt. Cardinality(T) < Cardinality(Nodes)
    BY <1>t, <1>nat
  <1>ph. \E x, y \in Nodes : x # y /\ f[x] = f[y]
    BY <1>f, <1>t, <1>lt, PigeonHole
  <1>qed. QED
    <2>1. PICK x, y \in Nodes : x # y /\ f[x] = f[y]
      BY <1>ph
    <2>2. Degree(x, G) = Degree(y, G)
      BY <2>1
    <2>3. QED
      BY <2>1, <2>2
=============================================================================
