---------------------------- MODULE GraphTheorem_line62 ----------------------------
EXTENDS Sets, TLAPS

Edges(Nodes) == { {m[1], m[2]} : m \in Nodes \X Nodes }

-------------------------------------------------------

NonLoopEdges(Nodes) == {e \in Edges(Nodes) : Cardinality(e) = 2}
SimpleGraphs(Nodes) == SUBSET NonLoopEdges(Nodes)
Degree(n, G) == Cardinality ({e \in G : n \in e})

------------------------------------------------------------------

\* Helper operator: edges at a specific node n.
EdgesAt(N, n) == { {n, x} : x \in N \ {n} }

\* Pair {a, b} of distinct nodes is a non-loop edge.
LEMMA PairIsEdge ==
  ASSUME NEW Nodes, NEW a \in Nodes, NEW b \in Nodes, a # b
  PROVE  {a, b} \in NonLoopEdges(Nodes)
PROOF
  <1>1. <<a, b>> \in Nodes \X Nodes
    OBVIOUS
  <1>2. <<a, b>>[1] = a /\ <<a, b>>[2] = b
    OBVIOUS
  <1>3. {<<a, b>>[1], <<a, b>>[2]} = {a, b}
    BY <1>2
  <1>4. \E mm \in Nodes \X Nodes : {a, b} = {mm[1], mm[2]}
    BY <1>1, <1>3
  <1>5. {a, b} \in Edges(Nodes)
    BY <1>4 DEF Edges
  <1>6. Cardinality({a, b}) = 2
    BY CardinalityTwo
  <1>7. QED
    BY <1>5, <1>6 DEF NonLoopEdges

\* Structure of a non-loop edge: it's a pair of distinct nodes.
LEMMA NonLoopEdgeStruct ==
  ASSUME NEW Nodes, NEW e \in NonLoopEdges(Nodes)
  PROVE  \E a, b \in Nodes : a # b /\ e = {a, b}
PROOF
  <1>1. e \in Edges(Nodes) /\ Cardinality(e) = 2
    BY DEF NonLoopEdges
  <1>2. PICK mm \in Nodes \X Nodes : e = {mm[1], mm[2]}
    BY <1>1 DEF Edges
  <1>3. mm[1] \in Nodes /\ mm[2] \in Nodes
    BY <1>2
  <1>4. mm[1] # mm[2]
    <2>1. SUFFICES ASSUME mm[1] = mm[2] PROVE FALSE
      OBVIOUS
    <2>2. {mm[1], mm[2]} = {mm[1]}
      BY <2>1
    <2>3. e = {mm[1]}
      BY <1>2, <2>2
    <2>4. Cardinality({mm[1]}) = 1
      BY CardinalityOne
    <2>5. Cardinality(e) = 1
      BY <2>3, <2>4
    <2>6. QED
      BY <1>1, <2>5
  <1>5. e = {mm[1], mm[2]}
    BY <1>2
  <1>6. QED
    BY <1>3, <1>4, <1>5

\* Given a non-loop edge containing n, the other endpoint exists.
LEMMA NonLoopOtherEnd ==
  ASSUME NEW Nodes, NEW e \in NonLoopEdges(Nodes), NEW n, n \in e
  PROVE  \E mm \in Nodes : mm # n /\ e = {n, mm}
PROOF
  <1>1. PICK a \in Nodes, b \in Nodes : a # b /\ e = {a, b}
    BY NonLoopEdgeStruct
  <1>2. n \in {a, b}
    BY <1>1
  <1>3. n = a \/ n = b
    BY <1>2
  <1>4. CASE n = a
    <2>1. b \in Nodes /\ b # n
      BY <1>1, <1>4
    <2>2. e = {n, b}
      BY <1>1, <1>4
    <2>3. QED
      BY <2>1, <2>2
  <1>5. CASE n = b
    <2>1. a \in Nodes /\ a # n
      BY <1>1, <1>5
    <2>2. e = {n, a}
      BY <1>1, <1>5
    <2>3. QED
      BY <2>1, <2>2
  <1>6. QED
    BY <1>3, <1>4, <1>5

\* EdgesAt equals {e in NonLoopEdges : n in e}.
LEMMA EdgesAt_Eq_NonLoopAt ==
  ASSUME NEW Nodes, NEW n \in Nodes
  PROVE  {e \in NonLoopEdges(Nodes) : n \in e} = EdgesAt(Nodes, n)
PROOF
  <1>1. ASSUME NEW e \in {ee \in NonLoopEdges(Nodes) : n \in ee}
        PROVE e \in EdgesAt(Nodes, n)
    <2>1. e \in NonLoopEdges(Nodes) /\ n \in e
      BY <1>1
    <2>2. PICK mm \in Nodes : mm # n /\ e = {n, mm}
      BY <2>1, NonLoopOtherEnd
    <2>3. mm \in Nodes \ {n}
      BY <2>2
    <2>4. QED
      BY <2>2, <2>3 DEF EdgesAt
  <1>2. ASSUME NEW e \in EdgesAt(Nodes, n)
        PROVE e \in {ee \in NonLoopEdges(Nodes) : n \in ee}
    <2>1. PICK mm \in Nodes \ {n} : e = {n, mm}
      BY <1>2 DEF EdgesAt
    <2>2. mm \in Nodes /\ mm # n
      BY <2>1
    <2>3. e \in NonLoopEdges(Nodes)
      BY <2>1, <2>2, PairIsEdge
    <2>4. n \in e
      BY <2>1
    <2>5. QED
      BY <2>3, <2>4
  <1>3. QED
    BY <1>1, <1>2

\* EdgesAt is a subset of SUBSET Nodes (each edge is a subset of Nodes).
LEMMA EdgesAt_SubsetPowerset ==
  ASSUME NEW Nodes, NEW n \in Nodes
  PROVE  EdgesAt(Nodes, n) \subseteq SUBSET Nodes
PROOF
  <1>1. SUFFICES ASSUME NEW e \in EdgesAt(Nodes, n)
                 PROVE e \in SUBSET Nodes
    OBVIOUS
  <1>2. PICK mm \in Nodes \ {n} : e = {n, mm}
    BY <1>1 DEF EdgesAt
  <1>3. mm \in Nodes
    BY <1>2
  <1>4. e \subseteq Nodes
    BY <1>2, <1>3
  <1>5. QED
    BY <1>4

\* EdgesAt is finite when Nodes is finite.
LEMMA EdgesAt_IsFiniteSet ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes), NEW n \in Nodes
  PROVE  IsFiniteSet(EdgesAt(Nodes, n))
PROOF
  <1>1. EdgesAt(Nodes, n) \subseteq SUBSET Nodes
    BY EdgesAt_SubsetPowerset
  <1>2. IsFiniteSet(SUBSET Nodes)
    BY SubsetsFinite
  <1>3. QED
    BY <1>1, <1>2, FiniteSubset

\* Cardinality of EdgesAt is |Nodes| - 1.
LEMMA EdgesAt_Cardinality ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes), NEW n \in Nodes
  PROVE  Cardinality(EdgesAt(Nodes, n)) = Cardinality(Nodes) - 1
PROOF
  <1> DEFINE f == [mm \in Nodes \ {n} |-> {n, mm}]
  <1>1. IsFiniteSet(Nodes \ {n}) /\
        Cardinality(Nodes \ {n}) = Cardinality(Nodes) - 1
    BY CardinalitySetMinus
  <1>2. IsFiniteSet(EdgesAt(Nodes, n))
    BY EdgesAt_IsFiniteSet
  <1>3. f \in [Nodes \ {n} -> EdgesAt(Nodes, n)]
    <2>1. SUFFICES ASSUME NEW mm \in Nodes \ {n}
                   PROVE f[mm] \in EdgesAt(Nodes, n)
      OBVIOUS
    <2>2. f[mm] = {n, mm}
      OBVIOUS
    <2>3. {n, mm} \in EdgesAt(Nodes, n)
      BY <2>1 DEF EdgesAt
    <2>4. QED
      BY <2>2, <2>3
  <1>4. \A x, y \in Nodes \ {n} : x # y => f[x] # f[y]
    <2>1. SUFFICES ASSUME NEW x \in Nodes \ {n}, NEW y \in Nodes \ {n},
                          f[x] = f[y]
                   PROVE x = y
      OBVIOUS
    <2>2. {n, x} = {n, y}
      BY <2>1
    <2>3. x \in {n, y}
      BY <2>2
    <2>4. x = n \/ x = y
      BY <2>3
    <2>5. x # n
      BY <2>1
    <2>6. QED
      BY <2>4, <2>5
  <1>5. \A y \in EdgesAt(Nodes, n) : \E x \in Nodes \ {n} : f[x] = y
    <2>1. SUFFICES ASSUME NEW y \in EdgesAt(Nodes, n)
                   PROVE \E x \in Nodes \ {n} : f[x] = y
      OBVIOUS
    <2>2. PICK mm \in Nodes \ {n} : y = {n, mm}
      BY <2>1 DEF EdgesAt
    <2>3. f[mm] = {n, mm}
      OBVIOUS
    <2>4. f[mm] = y
      BY <2>2, <2>3
    <2>5. QED
      BY <2>4
  <1>6. IsBijection(f, Nodes \ {n}, EdgesAt(Nodes, n))
    BY <1>3, <1>4, <1>5 DEF IsBijection
  <1>7. Cardinality(Nodes \ {n}) = Cardinality(EdgesAt(Nodes, n))
    BY <1>1, <1>2, <1>6, IsBijectionCardinality
  <1>8. QED
    BY <1>1, <1>7

\* Edges of G containing n is a subset of EdgesAt.
LEMMA EdgesInG_Subset_EdgesAt ==
  ASSUME NEW Nodes, NEW G \in SimpleGraphs(Nodes), NEW n \in Nodes
  PROVE  {e \in G : n \in e} \subseteq EdgesAt(Nodes, n)
PROOF
  <1>1. SUFFICES ASSUME NEW e \in {ee \in G : n \in ee}
                 PROVE e \in EdgesAt(Nodes, n)
    OBVIOUS
  <1>2. e \in G /\ n \in e
    BY <1>1
  <1>3. G \subseteq NonLoopEdges(Nodes)
    BY DEF SimpleGraphs
  <1>4. e \in NonLoopEdges(Nodes)
    BY <1>2, <1>3
  <1>5. e \in {ee \in NonLoopEdges(Nodes) : n \in ee}
    BY <1>2, <1>4
  <1>6. QED
    BY <1>5, EdgesAt_Eq_NonLoopAt

\* Degree upper bound.
LEMMA DegreeUpperBound ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes), NEW n \in Nodes
  PROVE  /\ IsFiniteSet({e \in G : n \in e})
         /\ Degree(n, G) \in Nat
         /\ Degree(n, G) <= Cardinality(Nodes) - 1
PROOF
  <1>1. {e \in G : n \in e} \subseteq EdgesAt(Nodes, n)
    BY EdgesInG_Subset_EdgesAt
  <1>2. IsFiniteSet(EdgesAt(Nodes, n))
    BY EdgesAt_IsFiniteSet
  <1>3. IsFiniteSet({e \in G : n \in e}) /\
        Cardinality({e \in G : n \in e}) <= Cardinality(EdgesAt(Nodes, n))
    BY <1>1, <1>2, FiniteSubset
  <1>4. Cardinality(EdgesAt(Nodes, n)) = Cardinality(Nodes) - 1
    BY EdgesAt_Cardinality
  <1>5. Degree(n, G) = Cardinality({e \in G : n \in e})
    BY DEF Degree
  <1>6. Degree(n, G) \in Nat
    BY <1>3, <1>5, CardinalityInNat
  <1>7. Degree(n, G) <= Cardinality(Nodes) - 1
    BY <1>3, <1>4, <1>5
  <1>8. QED
    BY <1>3, <1>6, <1>7

\* If there's an isolated vertex, then all degrees are at most |Nodes| - 2.
LEMMA DegreeWithIsolated ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes), Cardinality(Nodes) > 1,
         NEW G \in SimpleGraphs(Nodes),
         NEW n0 \in Nodes, Degree(n0, G) = 0,
         NEW m \in Nodes
  PROVE  Degree(m, G) <= Cardinality(Nodes) - 2
PROOF
  <1>0. Cardinality(Nodes) \in Nat
    BY CardinalityInNat
  <1>1. IsFiniteSet({e \in G : n0 \in e})
    BY DegreeUpperBound
  <1>2. Cardinality({e \in G : n0 \in e}) = 0
    BY DEF Degree
  <1>3. {e \in G : n0 \in e} = {}
    BY <1>1, <1>2, CardinalityZero
  <1>4. CASE m = n0
    <2>1. Degree(m, G) = 0
      BY <1>4
    <2>2. 0 <= Cardinality(Nodes) - 2
      BY <1>0
    <2>3. QED
      BY <2>1, <2>2
  <1>5. CASE m # n0
    <2>1. n0 \in Nodes \ {m}
      BY <1>5
    <2>2. {m, n0} \in EdgesAt(Nodes, m)
      BY <2>1 DEF EdgesAt
    <2>3. {m, n0} \notin G
      <3>1. SUFFICES ASSUME {m, n0} \in G PROVE FALSE
        OBVIOUS
      <3>2. n0 \in {m, n0}
        OBVIOUS
      <3>3. {m, n0} \in {e \in G : n0 \in e}
        BY <3>1, <3>2
      <3>4. QED
        BY <1>3, <3>3
    <2>4. {e \in G : m \in e} \subseteq EdgesAt(Nodes, m) \ {{m, n0}}
      <3>1. SUFFICES ASSUME NEW e \in {ee \in G : m \in ee}
                     PROVE e \in EdgesAt(Nodes, m) /\ e # {m, n0}
        OBVIOUS
      <3>2. e \in {ee \in G : m \in ee}
        BY <3>1
      <3>3. e \in EdgesAt(Nodes, m)
        BY <3>2, EdgesInG_Subset_EdgesAt
      <3>4. e \in G
        BY <3>1
      <3>5. e # {m, n0}
        BY <2>3, <3>4
      <3>6. QED
        BY <3>3, <3>5
    <2>5. IsFiniteSet(EdgesAt(Nodes, m))
      BY EdgesAt_IsFiniteSet
    <2>6. Cardinality(EdgesAt(Nodes, m)) = Cardinality(Nodes) - 1
      BY EdgesAt_Cardinality
    <2>7. IsFiniteSet(EdgesAt(Nodes, m) \ {{m, n0}}) /\
          Cardinality(EdgesAt(Nodes, m) \ {{m, n0}}) = Cardinality(EdgesAt(Nodes, m)) - 1
      BY <2>2, <2>5, CardinalitySetMinus
    <2>8. Cardinality(EdgesAt(Nodes, m) \ {{m, n0}}) = Cardinality(Nodes) - 2
      BY <1>0, <2>6, <2>7
    <2>9. IsFiniteSet({e \in G : m \in e}) /\
          Cardinality({e \in G : m \in e}) <= Cardinality(EdgesAt(Nodes, m) \ {{m, n0}})
      BY <2>4, <2>7, FiniteSubset
    <2>10. Degree(m, G) = Cardinality({e \in G : m \in e})
      BY DEF Degree
    <2>11. QED
      BY <2>8, <2>9, <2>10
  <1>6. QED
    BY <1>4, <1>5

------------------------------------------------------------------

THEOREM
  ASSUME NEW Nodes, IsFiniteSet(Nodes), Cardinality(Nodes) > 1,
         NEW G \in SimpleGraphs(Nodes)
  PROVE  \E m, n \in Nodes : /\ m # n
                             /\ Degree(m, G) = Degree(n, G)
PROOF
  <1>0. Cardinality(Nodes) \in Nat /\ Cardinality(Nodes) >= 2
    <2>1. Cardinality(Nodes) \in Nat
      BY CardinalityInNat
    <2>2. Cardinality(Nodes) >= 2
      BY <2>1
    <2>3. QED
      BY <2>1, <2>2
  <1> DEFINE f == [k \in Nodes |-> Degree(k, G)]
  <1>1. CASE \E nn \in Nodes : Degree(nn, G) = 0
    <2>1. PICK n0 \in Nodes : Degree(n0, G) = 0
      BY <1>1
    <2>2. \A k \in Nodes : Degree(k, G) \in 0..(Cardinality(Nodes) - 2)
      <3>1. SUFFICES ASSUME NEW k \in Nodes
                     PROVE Degree(k, G) \in 0..(Cardinality(Nodes) - 2)
        OBVIOUS
      <3>2. Degree(k, G) <= Cardinality(Nodes) - 2
        BY <2>1, DegreeWithIsolated
      <3>3. Degree(k, G) \in Nat
        BY DegreeUpperBound
      <3>4. Cardinality(Nodes) - 2 \in Nat
        BY <1>0
      <3>5. QED
        BY <3>2, <3>3, <3>4
    <2>3. f \in [Nodes -> 0..(Cardinality(Nodes) - 2)]
      BY <2>2
    <2>4. IsFiniteSet(0..(Cardinality(Nodes) - 2))
      <3>1. Cardinality(Nodes) - 2 \in Nat
        BY <1>0
      <3>2. 0 \in Nat
        OBVIOUS
      <3>3. QED
        BY <3>1, <3>2, IntervalCardinality
    <2>5. Cardinality(0..(Cardinality(Nodes) - 2)) = Cardinality(Nodes) - 1
      <3>1. Cardinality(Nodes) - 2 \in Nat
        BY <1>0
      <3>2. 0 \in Nat
        OBVIOUS
      <3>3. ~(0 > Cardinality(Nodes) - 2)
        BY <1>0
      <3>4. Cardinality(0..(Cardinality(Nodes) - 2)) =
            IF 0 > Cardinality(Nodes) - 2 THEN 0 ELSE (Cardinality(Nodes) - 2) - 0 + 1
        BY <3>1, <3>2, IntervalCardinality
      <3>5. Cardinality(0..(Cardinality(Nodes) - 2)) = (Cardinality(Nodes) - 2) - 0 + 1
        BY <3>3, <3>4
      <3>6. (Cardinality(Nodes) - 2) - 0 + 1 = Cardinality(Nodes) - 1
        BY <1>0
      <3>7. QED
        BY <3>5, <3>6
    <2>6. Cardinality(0..(Cardinality(Nodes) - 2)) < Cardinality(Nodes)
      BY <2>5, <1>0
    <2>7. \E x, y \in Nodes : x # y /\ f[x] = f[y]
      BY <2>3, <2>4, <2>6, PigeonHole
    <2>8. PICK x \in Nodes, y \in Nodes : x # y /\ f[x] = f[y]
      BY <2>7
    <2>9. Degree(x, G) = Degree(y, G)
      BY <2>8
    <2>10. QED
      BY <2>8, <2>9
  <1>2. CASE \A nn \in Nodes : Degree(nn, G) # 0
    <2>1. \A k \in Nodes : Degree(k, G) \in 1..(Cardinality(Nodes) - 1)
      <3>1. SUFFICES ASSUME NEW k \in Nodes
                     PROVE Degree(k, G) \in 1..(Cardinality(Nodes) - 1)
        OBVIOUS
      <3>2. Degree(k, G) <= Cardinality(Nodes) - 1
        BY DegreeUpperBound
      <3>3. Degree(k, G) \in Nat
        BY DegreeUpperBound
      <3>4. Degree(k, G) # 0
        BY <1>2
      <3>5. Degree(k, G) >= 1
        BY <3>3, <3>4
      <3>6. Cardinality(Nodes) - 1 \in Nat
        BY <1>0
      <3>7. QED
        BY <3>2, <3>3, <3>5, <3>6
    <2>2. f \in [Nodes -> 1..(Cardinality(Nodes) - 1)]
      BY <2>1
    <2>3. IsFiniteSet(1..(Cardinality(Nodes) - 1))
      <3>1. Cardinality(Nodes) - 1 \in Nat
        BY <1>0
      <3>2. 1 \in Nat
        OBVIOUS
      <3>3. QED
        BY <3>1, <3>2, IntervalCardinality
    <2>4. Cardinality(1..(Cardinality(Nodes) - 1)) = Cardinality(Nodes) - 1
      <3>1. Cardinality(Nodes) - 1 \in Nat
        BY <1>0
      <3>2. 1 \in Nat
        OBVIOUS
      <3>3. ~(1 > Cardinality(Nodes) - 1)
        BY <1>0
      <3>4. Cardinality(1..(Cardinality(Nodes) - 1)) =
            IF 1 > Cardinality(Nodes) - 1 THEN 0 ELSE (Cardinality(Nodes) - 1) - 1 + 1
        BY <3>1, <3>2, IntervalCardinality
      <3>5. Cardinality(1..(Cardinality(Nodes) - 1)) = (Cardinality(Nodes) - 1) - 1 + 1
        BY <3>3, <3>4
      <3>6. (Cardinality(Nodes) - 1) - 1 + 1 = Cardinality(Nodes) - 1
        BY <1>0
      <3>7. QED
        BY <3>5, <3>6
    <2>5. Cardinality(1..(Cardinality(Nodes) - 1)) < Cardinality(Nodes)
      BY <2>4, <1>0
    <2>6. \E x, y \in Nodes : x # y /\ f[x] = f[y]
      BY <2>2, <2>3, <2>5, PigeonHole
    <2>7. PICK x \in Nodes, y \in Nodes : x # y /\ f[x] = f[y]
      BY <2>6
    <2>8. Degree(x, G) = Degree(y, G)
      BY <2>7
    <2>9. QED
      BY <2>7, <2>8
  <1>3. QED
    BY <1>1, <1>2
=============================================================================
