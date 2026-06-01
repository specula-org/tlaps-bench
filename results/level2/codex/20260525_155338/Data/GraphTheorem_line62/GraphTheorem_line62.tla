---------------------------- MODULE GraphTheorem_line62 ----------------------------
EXTENDS Sets, TLAPS

Edges(Nodes) == { {m[1], m[2]} : m \in Nodes \X Nodes }

-------------------------------------------------------

NonLoopEdges(Nodes) == {e \in Edges(Nodes) : Cardinality(e) = 2}
SimpleGraphs(Nodes) == SUBSET NonLoopEdges(Nodes)
Degree(n, G) == Cardinality ({e \in G : n \in e})

------------------------------------------------------------------

Incident(n, G) == {e \in G : n \in e}
Other(n, e) == CHOOSE x : /\ x # n
                            /\ e = {n, x}
OtherSet(n, G) == {Other(n, e) : e \in Incident(n, G)}
DegFun(Nodes, G) == [n \in Nodes |-> Degree(n, G)]
DegTarget(Nodes, G) ==
  IF \E n \in Nodes : Degree(n, G) = 0
  THEN 0 .. (Cardinality(Nodes) - 2)
  ELSE 1 .. (Cardinality(Nodes) - 1)

LEMMA NonLoopEdgesSubsetNodes ==
  \A Nodes : NonLoopEdges(Nodes) \subseteq SUBSET Nodes
PROOF
  BY DEF NonLoopEdges, Edges

LEMMA SimpleGraphFinite ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes)
  PROVE  IsFiniteSet(G)
PROOF
  <1>1. IsFiniteSet(SUBSET Nodes)
    BY SubsetsFinite
  <1>2. NonLoopEdges(Nodes) \subseteq SUBSET Nodes
    BY NonLoopEdgesSubsetNodes
  <1>3. G \subseteq SUBSET Nodes
    BY <1>2 DEF SimpleGraphs
  <1>4. G \in SUBSET (SUBSET Nodes)
    BY <1>3
  <1>5. /\ IsFiniteSet(G)
        /\ Cardinality(G) \leq Cardinality(SUBSET Nodes)
    BY <1>1, <1>4, FiniteSubset
  <1> QED BY <1>5

LEMMA IncidentFinite ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n
  PROVE  IsFiniteSet(Incident(n, G))
PROOF
  <1>1. IsFiniteSet(G)
    BY SimpleGraphFinite
  <1>2. Incident(n, G) \subseteq G
    BY DEF Incident
  <1>3. Incident(n, G) \in SUBSET G
    BY <1>2
  <1>4. /\ IsFiniteSet(Incident(n, G))
        /\ Cardinality(Incident(n, G)) \leq Cardinality(G)
    BY <1>1, <1>3, FiniteSubset
  <1> QED BY <1>4

LEMMA TwoSetWithElem ==
  ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 2,
         NEW n \in S
  PROVE  \E x : /\ x # n
                /\ S = {n, x}
PROOF
  <1>1. /\ IsFiniteSet(S \ {n})
        /\ Cardinality(S \ {n}) = Cardinality(S) - 1
    BY CardinalitySetMinus
  <1>2. Cardinality(S \ {n}) = 1
    BY <1>1
  <1>3. \E x : S \ {n} = {x}
    BY <1>1, <1>2, CardinalityOneConverse
  <1>4. PICK x : S \ {n} = {x}
    BY <1>3
  <1>5. x # n
    BY <1>4
  <1>6. S = {n, x}
    BY <1>4
  <1> QED BY <1>5, <1>6

LEMMA IncidentEdgePair ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes,
         NEW e \in Incident(n, G)
  PROVE  \E x \in Nodes : /\ x # n
                         /\ e = {n, x}
PROOF
  <1>1. e \in NonLoopEdges(Nodes)
    BY DEF Incident, SimpleGraphs
  <1>2. e \in SUBSET Nodes
    BY <1>1, NonLoopEdgesSubsetNodes
  <1>3. /\ IsFiniteSet(e)
        /\ Cardinality(e) \leq Cardinality(Nodes)
    BY <1>2, FiniteSubset
  <1>4. Cardinality(e) = 2
    BY <1>1 DEF NonLoopEdges
  <1>5. \E x : /\ x # n
                /\ e = {n, x}
    BY <1>3, <1>4, TwoSetWithElem DEF Incident
  <1>6. PICK x : /\ x # n
                  /\ e = {n, x}
    BY <1>5
  <1>7. x \in Nodes
    BY <1>2, <1>6
  <1> QED BY <1>6, <1>7

LEMMA IncidentOther ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes,
         NEW e \in Incident(n, G)
  PROVE  /\ Other(n, e) \in Nodes \ {n}
         /\ e = {n, Other(n, e)}
PROOF
  <1>1. \E x \in Nodes : /\ x # n
                         /\ e = {n, x}
    BY IncidentEdgePair
  <1>2. \E x : /\ x # n
                /\ e = {n, x}
    BY <1>1
  <1>3. /\ Other(n, e) # n
        /\ e = {n, Other(n, e)}
    BY <1>2 DEF Other
  <1>4. Other(n, e) \in Nodes
    BY <1>1, <1>3
  <1> QED BY <1>3, <1>4

LEMMA OtherSetSubset ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes
  PROVE  OtherSet(n, G) \subseteq Nodes \ {n}
PROOF
  <1>1. ASSUME NEW x \in OtherSet(n, G)
        PROVE  x \in Nodes \ {n}
    <2>1. PICK e \in Incident(n, G) : x = Other(n, e)
      BY <1>1 DEF OtherSet
    <2>2. Other(n, e) \in Nodes \ {n}
      BY <2>1, IncidentOther
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1

LEMMA IncidentOtherBijection ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes
  PROVE  IsBijection([e \in Incident(n, G) |-> Other(n, e)],
                     Incident(n, G),
                     OtherSet(n, G))
PROOF
  <1>1. [e \in Incident(n, G) |-> Other(n, e)]
          \in [Incident(n, G) -> OtherSet(n, G)]
    BY DEF OtherSet
  <1>2. \A e1, e2 \in Incident(n, G) :
          (e1 # e2) => 
            ([e \in Incident(n, G) |-> Other(n, e)][e1] #
             [e \in Incident(n, G) |-> Other(n, e)][e2])
    <2>1. ASSUME NEW e1 \in Incident(n, G),
                 NEW e2 \in Incident(n, G),
                 e1 # e2
          PROVE  [e \in Incident(n, G) |-> Other(n, e)][e1] #
                 [e \in Incident(n, G) |-> Other(n, e)][e2]
      <3>1. /\ e1 = {n, Other(n, e1)}
            /\ e2 = {n, Other(n, e2)}
        BY <2>1, IncidentOther
      <3> QED BY <2>1, <3>1
    <2> QED BY <2>1
  <1>3. \A y \in OtherSet(n, G) :
          \E e \in Incident(n, G) :
            [e0 \in Incident(n, G) |-> Other(n, e0)][e] = y
    BY DEF OtherSet
  <1> QED BY <1>1, <1>2, <1>3 DEF IsBijection

LEMMA DegreeUpperBound ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes
  PROVE  Degree(n, G) <= Cardinality(Nodes) - 1
PROOF
  <1>1. IsFiniteSet(Incident(n, G))
    BY IncidentFinite
  <1>2. OtherSet(n, G) \subseteq Nodes \ {n}
    BY OtherSetSubset
  <1>3. OtherSet(n, G) \in SUBSET (Nodes \ {n})
    BY <1>2
  <1>4. /\ IsFiniteSet(Nodes \ {n})
        /\ Cardinality(Nodes \ {n}) = Cardinality(Nodes) - 1
    BY CardinalitySetMinus
  <1>5. /\ IsFiniteSet(OtherSet(n, G))
        /\ Cardinality(OtherSet(n, G)) <= Cardinality(Nodes \ {n})
    BY <1>3, <1>4, FiniteSubset
  <1>6. IsBijection([e \in Incident(n, G) |-> Other(n, e)],
                    Incident(n, G),
                    OtherSet(n, G))
    BY IncidentOtherBijection
  <1>7. Cardinality(Incident(n, G)) = Cardinality(OtherSet(n, G))
    BY <1>1, <1>5, <1>6, IsBijectionCardinality
  <1>8. Cardinality(Incident(n, G)) <= Cardinality(Nodes) - 1
    BY <1>4, <1>5, <1>7
  <1> QED BY <1>8 DEF Degree, Incident

LEMMA OtherSetMissingSubset ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes,
         NEW p \in Nodes,
         p # n,
         {n, p} \notin G
  PROVE  OtherSet(n, G) \subseteq ((Nodes \ {n}) \ {p})
PROOF
  <1>1. ASSUME NEW x \in OtherSet(n, G)
        PROVE  x \in ((Nodes \ {n}) \ {p})
    <2>1. PICK e \in Incident(n, G) : x = Other(n, e)
      BY <1>1 DEF OtherSet
    <2>2. /\ Other(n, e) \in Nodes \ {n}
          /\ e = {n, Other(n, e)}
      BY <2>1, IncidentOther
    <2>3. x \in Nodes \ {n}
      BY <2>1, <2>2
    <2>4. x # p
      BY <2>1, <2>2 DEF Incident
    <2> QED BY <2>3, <2>4
  <1> QED BY <1>1

LEMMA DegreeBoundMissingNeighbor ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes,
         NEW p \in Nodes,
         p # n,
         {n, p} \notin G
  PROVE  Degree(n, G) <= Cardinality(Nodes) - 2
PROOF
  <1>1. IsFiniteSet(Incident(n, G))
    BY IncidentFinite
  <1>2. /\ IsFiniteSet(Nodes \ {n})
        /\ Cardinality(Nodes \ {n}) = Cardinality(Nodes) - 1
    BY CardinalitySetMinus
  <1>3. p \in Nodes \ {n}
    BY <1>2
  <1>4. /\ IsFiniteSet((Nodes \ {n}) \ {p})
        /\ Cardinality((Nodes \ {n}) \ {p}) =
             Cardinality(Nodes \ {n}) - 1
    BY <1>2, <1>3, CardinalitySetMinus
  <1>5. Cardinality(Nodes) \in Nat
    BY CardinalityInNat
  <1>6. (Cardinality(Nodes) - 1) - 1 = Cardinality(Nodes) - 2
    BY <1>5, SMT
  <1>7. Cardinality((Nodes \ {n}) \ {p}) = Cardinality(Nodes) - 2
    BY <1>2, <1>4, <1>6
  <1>8. OtherSet(n, G) \subseteq ((Nodes \ {n}) \ {p})
    BY OtherSetMissingSubset
  <1>9. OtherSet(n, G) \in SUBSET ((Nodes \ {n}) \ {p})
    BY <1>8
  <1>10. /\ IsFiniteSet(OtherSet(n, G))
        /\ Cardinality(OtherSet(n, G))
             <= Cardinality((Nodes \ {n}) \ {p})
    BY <1>4, <1>9, FiniteSubset
  <1>11. IsBijection([e \in Incident(n, G) |-> Other(n, e)],
                    Incident(n, G),
                    OtherSet(n, G))
    BY IncidentOtherBijection
  <1>12. Cardinality(Incident(n, G)) = Cardinality(OtherSet(n, G))
    BY <1>1, <1>10, <1>11, IsBijectionCardinality
  <1>13. Cardinality(Incident(n, G)) <= Cardinality(Nodes) - 2
    BY <1>7, <1>10, <1>12
  <1> QED BY <1>13 DEF Degree, Incident

LEMMA ZeroDegreeNoIncident ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes,
         Degree(n, G) = 0
  PROVE  Incident(n, G) = {}
PROOF
  <1>1. IsFiniteSet(Incident(n, G))
    BY IncidentFinite
  <1>2. Cardinality(Incident(n, G)) = 0
    BY DEF Degree, Incident
  <1> QED BY <1>1, <1>2, CardinalityZero

LEMMA ZeroDegreeMissingEdge ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW z \in Nodes,
         NEW n \in Nodes,
         z # n,
         Degree(z, G) = 0
  PROVE  {n, z} \notin G
PROOF
  <1>1. Incident(z, G) = {}
    BY ZeroDegreeNoIncident
  <1> QED BY <1>1 DEF Incident

LEMMA IntervalZeroToKMinusTwo ==
  ASSUME NEW k \in Nat, k > 1
  PROVE  /\ IsFiniteSet(0 .. (k - 2))
         /\ Cardinality(0 .. (k - 2)) = k - 1
PROOF
  <1>1. k - 2 \in Nat
    BY SMT
  <1>2. /\ IsFiniteSet(0 .. (k - 2))
        /\ Cardinality(0 .. (k - 2)) =
             IF 0 > k - 2 THEN 0 ELSE (k - 2) - 0 + 1
    BY <1>1, IntervalCardinality
  <1>3. ~(0 > k - 2)
    BY SMT
  <1>4. (k - 2) - 0 + 1 = k - 1
    BY SMT
  <1> QED BY <1>2, <1>3, <1>4

LEMMA IntervalOneToKMinusOne ==
  ASSUME NEW k \in Nat, k > 1
  PROVE  /\ IsFiniteSet(1 .. (k - 1))
         /\ Cardinality(1 .. (k - 1)) = k - 1
PROOF
  <1>1. k - 1 \in Nat
    BY SMT
  <1>2. /\ IsFiniteSet(1 .. (k - 1))
        /\ Cardinality(1 .. (k - 1)) =
             IF 1 > k - 1 THEN 0 ELSE (k - 1) - 1 + 1
    BY <1>1, IntervalCardinality
  <1>3. ~(1 > k - 1)
    BY SMT
  <1>4. (k - 1) - 1 + 1 = k - 1
    BY SMT
  <1> QED BY <1>2, <1>3, <1>4

LEMMA DegreeNat ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW G \in SimpleGraphs(Nodes),
         NEW n \in Nodes
  PROVE  Degree(n, G) \in Nat
PROOF
  <1>1. IsFiniteSet(Incident(n, G))
    BY IncidentFinite
  <1>2. Cardinality(Incident(n, G)) \in Nat
    BY <1>1, CardinalityInNat
  <1> QED BY <1>2 DEF Degree, Incident

LEMMA DegTargetFinite ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes), Cardinality(Nodes) > 1,
         NEW G \in SimpleGraphs(Nodes)
  PROVE  /\ IsFiniteSet(DegTarget(Nodes, G))
         /\ Cardinality(DegTarget(Nodes, G)) < Cardinality(Nodes)
PROOF
  <1>1. Cardinality(Nodes) \in Nat
    BY CardinalityInNat
  <1>2. CASE \E n \in Nodes : Degree(n, G) = 0
    <2>1. DegTarget(Nodes, G) = 0 .. (Cardinality(Nodes) - 2)
      BY <1>2 DEF DegTarget
    <2>2. /\ IsFiniteSet(0 .. (Cardinality(Nodes) - 2))
          /\ Cardinality(0 .. (Cardinality(Nodes) - 2)) =
               Cardinality(Nodes) - 1
      BY <1>1, IntervalZeroToKMinusTwo
    <2> QED BY <2>1, <2>2, <1>1, SMT
  <1>3. CASE ~(\E n \in Nodes : Degree(n, G) = 0)
    <2>1. DegTarget(Nodes, G) = 1 .. (Cardinality(Nodes) - 1)
      BY <1>3 DEF DegTarget
    <2>2. /\ IsFiniteSet(1 .. (Cardinality(Nodes) - 1))
          /\ Cardinality(1 .. (Cardinality(Nodes) - 1)) =
               Cardinality(Nodes) - 1
      BY <1>1, IntervalOneToKMinusOne
    <2> QED BY <2>1, <2>2, <1>1, SMT
  <1> QED BY <1>2, <1>3

LEMMA DegFunInTarget ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes), Cardinality(Nodes) > 1,
         NEW G \in SimpleGraphs(Nodes)
  PROVE  DegFun(Nodes, G) \in [Nodes -> DegTarget(Nodes, G)]
PROOF
  <1>1. Cardinality(Nodes) \in Nat
    BY CardinalityInNat
  <1>2. CASE \E z \in Nodes : Degree(z, G) = 0
    <2>1. PICK z \in Nodes : Degree(z, G) = 0
      BY <1>2
    <2>2. \A n \in Nodes : Degree(n, G) \in 0 .. (Cardinality(Nodes) - 2)
      <3>1. ASSUME NEW n \in Nodes
            PROVE  Degree(n, G) \in 0 .. (Cardinality(Nodes) - 2)
        <4>1. Degree(n, G) \in Nat
          BY DegreeNat
        <4>2. CASE n = z
          BY <2>1, <4>2, <1>1, SMT
        <4>3. CASE n # z
          <5>1. {n, z} \notin G
            BY <2>1, <4>3, ZeroDegreeMissingEdge
          <5>2. Degree(n, G) <= Cardinality(Nodes) - 2
            BY <4>3, <5>1, DegreeBoundMissingNeighbor
          <5> QED BY <4>1, <5>2, SMT
        <4> QED BY <4>2, <4>3
      <3> QED BY <3>1
    <2>3. DegTarget(Nodes, G) = 0 .. (Cardinality(Nodes) - 2)
      BY <1>2 DEF DegTarget
    <2> QED BY <2>2, <2>3 DEF DegFun
  <1>3. CASE ~(\E z \in Nodes : Degree(z, G) = 0)
    <2>1. \A n \in Nodes : Degree(n, G) \in 1 .. (Cardinality(Nodes) - 1)
      <3>1. ASSUME NEW n \in Nodes
            PROVE  Degree(n, G) \in 1 .. (Cardinality(Nodes) - 1)
        <4>1. Degree(n, G) \in Nat
          BY DegreeNat
        <4>2. Degree(n, G) # 0
          BY <1>3
        <4>3. 1 <= Degree(n, G)
          BY <4>1, <4>2, SMT
        <4>4. Degree(n, G) <= Cardinality(Nodes) - 1
          BY DegreeUpperBound
        <4> QED BY <4>1, <4>3, <4>4, SMT
      <3> QED BY <3>1
    <2>2. DegTarget(Nodes, G) = 1 .. (Cardinality(Nodes) - 1)
      BY <1>3 DEF DegTarget
    <2> QED BY <2>1, <2>2 DEF DegFun
  <1> QED BY <1>2, <1>3

THEOREM
  ASSUME NEW Nodes, IsFiniteSet(Nodes), Cardinality(Nodes) > 1,
         NEW G \in SimpleGraphs(Nodes)
  PROVE  \E m, n \in Nodes : /\ m # n
                             /\ Degree(m, G) = Degree(n, G)
PROOF
  <1>1. /\ IsFiniteSet(DegTarget(Nodes, G))
        /\ Cardinality(DegTarget(Nodes, G)) < Cardinality(Nodes)
    BY DegTargetFinite
  <1>2. DegFun(Nodes, G) \in [Nodes -> DegTarget(Nodes, G)]
    BY DegFunInTarget
  <1>3. \E m, n \in Nodes :
           /\ m # n
           /\ DegFun(Nodes, G)[m] = DegFun(Nodes, G)[n]
    BY <1>1, <1>2, PigeonHole
  <1>4. PICK m, n \in Nodes :
           /\ m # n
           /\ DegFun(Nodes, G)[m] = DegFun(Nodes, G)[n]
    BY <1>3
  <1> QED BY <1>4 DEF DegFun
=============================================================================
