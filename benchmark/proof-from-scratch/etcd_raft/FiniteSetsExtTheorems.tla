-------------------------- MODULE FiniteSetsExtTheorems -------------------
EXTENDS FiniteSetsExt, FiniteSets, Integers








THEOREM FoldSetEmpty ==
    ASSUME NEW op(_,_), NEW base
    PROVE  FoldSet(op, base, {}) = base






THEOREM FoldSetNonempty ==
    ASSUME NEW op(_,_), NEW base, NEW S, S # {}, IsFiniteSet(S)
    PROVE  \E x \in S : FoldSet(op, base, S) = op(x, FoldSet(op, base, S \ {x}))





THEOREM FoldSetType ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           \A t,u \in Typ : op(t,u) \in Typ
    PROVE  FoldSet(op, base, S) \in Typ







THEOREM FoldSetAC ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW x \in S
    PROVE  FoldSet(op, base, S) = op(x, FoldSet(op, base, S \ {x}))


THEOREM FoldSetACAddElement ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW x \in Typ \ S
    PROVE  FoldSet(op, base, S \union {x}) = op(x, FoldSet(op, base, S))





THEOREM FoldSetDisjointUnion ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           \A t \in Typ : op(base, t) = t,
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW T \in SUBSET Typ, IsFiniteSet(T), S \cap T = {}
    PROVE  FoldSet(op, base, S \union T) = 
           op(FoldSet(op, base, S), FoldSet(op, base, T))

---------------------------------------------------------------------------





THEOREM SumSetNat ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  SumSet(S) \in Nat

THEOREM SumSetInt ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  SumSet(S) \in Int




THEOREM SumSetEmpty == SumSet({}) = 0





THEOREM SumSetNonempty ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S 
    PROVE  SumSet(S) = x + SumSet(S \ {x})


THEOREM SumSetAddElement ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in Int \ S
    PROVE  SumSet(S \union {x}) = x + SumSet(S)




THEOREM SumSetDisjointUnion ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S),
           NEW T \in SUBSET Int, IsFiniteSet(T), S \cap T = {}
    PROVE  SumSet(S \union T) = SumSet(S) + SumSet(T)





THEOREM SumSetNatSubset ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S),
           NEW T \in SUBSET S
    PROVE  SumSet(T) <= SumSet(S)





THEOREM SumSetNatZero ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  SumSet(S) = 0 <=> S \subseteq {0}

---------------------------------------------------------------------------





THEOREM ProductSetNat ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  ProductSet(S) \in Nat

THEOREM ProductSetInt ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  ProductSet(S) \in Int




THEOREM ProductSetEmpty == ProductSet({}) = 1





THEOREM ProductSetNonempty ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S 
    PROVE  ProductSet(S) = x * ProductSet(S \ {x})


THEOREM ProductSetAddElement ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in Int \ S
    PROVE  ProductSet(S \union {x}) = x * ProductSet(S)




THEOREM ProductSetDisjointUnion ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S),
           NEW T \in SUBSET Int, IsFiniteSet(T), S \cap T = {}
    PROVE  ProductSet(S \union T) = ProductSet(S) * ProductSet(T)





THEOREM ProductSetNatOne ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  ProductSet(S) = 1 <=> S \subseteq {1}




THEOREM ProductSetZero ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  ProductSet(S) = 0 <=> 0 \in S 





THEOREM ProductSetNatSubset ==
    ASSUME NEW S \in SUBSET Nat \ {0}, IsFiniteSet(S),
           NEW T \in SUBSET S
    PROVE  ProductSet(T) <= ProductSet(S)

---------------------------------------------------------------------------





THEOREM MapThenSumSetNat ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Nat
    PROVE  MapThenSumSet(op, S) \in Nat

THEOREM MapThenSumSetInt ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Int
    PROVE  MapThenSumSet(op, S) \in Int




THEOREM MapThenSumSetEmpty == 
    ASSUME NEW op(_)
    PROVE  MapThenSumSet(op, {}) = 0





THEOREM MapThenSumSetNonempty ==
    ASSUME NEW S, IsFiniteSet(S), NEW x \in S,
           NEW op(_), \A s \in S : op(s) \in Int
    PROVE  MapThenSumSet(op, S) = op(x) + MapThenSumSet(op, S \ {x})


THEOREM MapThenSumSetAddElement ==
    ASSUME NEW S, IsFiniteSet(S), NEW x, x \notin S,
           NEW op(_), \A s \in S \union {x} : op(s) \in Int
    PROVE  MapThenSumSet(op, S \union {x}) = op(x) + MapThenSumSet(op, S)





THEOREM MapThenSumSetDisjointUnion ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW T, IsFiniteSet(T), S \cap T = {},
           NEW op(_), \A x \in S \union T : op(x) \in Int
    PROVE  MapThenSumSet(op, S \union T) = 
           MapThenSumSet(op, S) + MapThenSumSet(op, T)





THEOREM MapThenSumSetNatSubset ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW T \in SUBSET S,
           NEW op(_), \A x \in S : op(x) \in Nat
    PROVE  MapThenSumSet(op, T) <= MapThenSumSet(op, S)





THEOREM MapThenSumSetZero ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Nat 
    PROVE  MapThenSumSet(op, S) = 0 <=> \A s \in S : op(s) = 0





THEOREM MapThenSumSetMonotonic ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A s \in S : f(s) \in Int,
           NEW g(_), \A s \in S : g(s) \in Int,
           \A s \in S : f(s) <= g(s)
    PROVE  MapThenSumSet(f, S) <= MapThenSumSet(g, S)





THEOREM MapThenSumSetStrictlyMonotonic ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A s \in S : f(s) \in Int,
           NEW g(_), \A s \in S : g(s) \in Int,
           \A s \in S : f(s) <= g(s),
           NEW s \in S, f(s) < g(s)
    PROVE  MapThenSumSet(f, S) < MapThenSumSet(g, S)

---------------------------------------------------------------------------








THEOREM MaxInt ==
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x >= y
    PROVE  Max(S) = x




THEOREM MaxIntFinite ==
    ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
    PROVE  /\ Max(S) \in S
           /\ \A y \in S : Max(S) >= y




THEOREM MaxIntBounded ==
    ASSUME NEW S \in SUBSET Int, S # {}, NEW x \in Int, \A y \in S : x >= y
    PROVE  /\ Max(S) \in S 
           /\ \A y \in S : Max(S) >= y




THEOREM MaxInterval ==
    ASSUME NEW a \in Int, NEW b \in Int, a <= b 
    PROVE  Max(a..b) = b




THEOREM MinInt ==
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x <= y
    PROVE  Min(S) = x




THEOREM MinIntFinite ==
    ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
    PROVE  /\ Min(S) \in S
           /\ \A y \in S : Min(S) <= y




THEOREM MinIntBounded ==
    ASSUME NEW S \in SUBSET Int, S # {}, NEW x \in Int, \A y \in S : x <= y
    PROVE  /\ Min(S) \in S 
           /\ \A y \in S : Min(S) <= y




THEOREM MinInterval ==
    ASSUME NEW a \in Int, NEW b \in Int, a <= b 
    PROVE  Min(a..b) = a




THEOREM MinNat ==
    ASSUME NEW S \in SUBSET Nat, S # {}
    PROVE  /\ Min(S) \in S 
           /\ \A y \in S : Min(S) <= y


===========================================================================
