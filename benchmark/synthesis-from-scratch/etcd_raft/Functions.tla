------------------------------ MODULE Functions -----------------------------







EXTENDS Integers, Folds




Restrict(f,S) == [ x \in S |-> f[x] ]










RestrictDomain(f, Test(_)) == Restrict(f, {x \in DOMAIN f : Test(x)})


















RestrictValues(f, Test(_)) ==
  LET S == {x \in DOMAIN f : Test(f[x])}
  IN  Restrict(f, S)














IsRestriction(narrow, wide) ==
    /\ DOMAIN narrow \subseteq DOMAIN wide 
    /\ \A x \in DOMAIN narrow \intersect DOMAIN wide: narrow[x] = wide[x]






Range(f) == { f[x] : x \in DOMAIN f }










Pointwise(f, g, T(_,_)) == [ e \in DOMAIN f |-> T(f[e], g[e]) ]












Inverse(f,S,T) == [t \in T |-> CHOOSE s \in S : t \in Range(f) => f[s] = t]




AntiFunction(f) == Inverse(f, DOMAIN f, Range(f))








IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b




Injection(S,T) == { M \in [S -> T] : IsInjective(M) }






Surjection(S,T) == { M \in [S -> T] : \A t \in T : \E s \in S : M[s] = t }





Bijection(S,T) == Injection(S,T) \cap Surjection(S,T)






ExistsInjection(S,T)  == Injection(S,T) # {}
ExistsSurjection(S,T) == Surjection(S,T) # {}
ExistsBijection(S,T)  == Bijection(S,T) # {}

--------------------------------------------------------------------------------














FoldFunctionOnSet(op(_,_), base, fun, indices) ==
  MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s: CHOOSE x \in s : TRUE, indices)









FoldFunction(op(_,_), base, fun) ==
  FoldFunctionOnSet(op, base, fun, DOMAIN fun)








SumFunctionOnSet(fun, indices) == FoldFunctionOnSet(+, 0, fun, indices)
SumFunction(fun) == SumFunctionOnSet(fun, DOMAIN fun)

=============================================================================

