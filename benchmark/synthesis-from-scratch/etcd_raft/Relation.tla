----------------------------- MODULE Relation ------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets





























IsReflexive(R, S) == \A x \in S : R[x,x]

IsReflexiveUnder(op(_,_), S) ==



    IsReflexive([p \in S \X S |-> op(p[1], p[2])], S)











IsIrreflexive(R, S) == \A x \in S : ~ R[x,x]

IsIrreflexiveUnder(op(_,_), S) ==



    IsIrreflexive([p \in S \X S |-> op(p[1], p[2])], S)










IsSymmetric(R, S) == \A x,y \in S : R[x,y] <=> R[y,x]

IsSymmetricUnder(op(_,_), S) ==



    IsSymmetric([p \in S \X S |-> op(p[1], p[2])], S)











IsAntiSymmetric(R, S) == \A x,y \in S : R[x,y] /\ R[y,x] => x=y

IsAntiSymmetricUnder(op(_,_), S) ==



    IsAntiSymmetric([p \in S \X S |-> op(p[1], p[2])], S)











IsAsymmetric(R, S) == \A x,y \in S : ~(R[x,y] /\ R[y,x])

IsAsymmetricUnder(op(_,_), S) ==



    IsAsymmetric([p \in S \X S |-> op(p[1], p[2])], S)











IsTransitive(R, S) == \A x,y,z \in S : R[x,y] /\ R[y,z] => R[x,z]

IsTransitiveUnder(op(_,_), S) ==



    IsTransitive([p \in S \X S |-> op(p[1], p[2])], S)











IsStrictlyPartiallyOrdered(R, S) ==
    /\ IsIrreflexive(R, S)
    /\ IsAntiSymmetric(R, S)
    /\ IsTransitive(R, S)

IsStrictlyPartiallyOrderedUnder(op(_,_), S) ==



    IsStrictlyPartiallyOrdered([p \in S \X S |-> op(p[1], p[2])], S)











IsPartiallyOrdered(R, S) ==
    /\ IsReflexive(R, S)
    /\ IsAntiSymmetric(R, S)
    /\ IsTransitive(R, S)

IsPartiallyOrderedUnder(op(_,_), S) ==



    IsPartiallyOrdered([p \in S \X S |-> op(p[1], p[2])], S)










IsStrictlyTotallyOrdered(R, S) ==
    /\ IsStrictlyPartiallyOrdered(R, S)
    
    /\ \A x,y \in S : x # y => R[x,y] \/ R[y,x]

IsStrictlyTotallyOrderedUnder(op(_,_), S) ==



    IsStrictlyTotallyOrdered([p \in S \X S |-> op(p[1], p[2])], S)









IsTotallyOrdered(R, S) ==
    /\ IsPartiallyOrdered(R, S)
    /\ \A x,y \in S : R[x,y] \/ R[y,x]

IsTotallyOrderedUnder(op(_,_), S) ==



    IsTotallyOrdered([p \in S \X S |-> op(p[1], p[2])], S)




TransitiveClosure(R, S) ==
  LET N == Cardinality(S)
      trcl[n \in Nat] == 
          [x,y \in S |-> IF n=0 THEN R[x,y]
                         ELSE \/ trcl[n-1][x,y]
                              \/ \E z \in S : trcl[n-1][x,z] /\ trcl[n-1][z,y]]
  IN  trcl[N]




ReflexiveTransitiveClosure(R, S) ==
  LET trcl == TransitiveClosure(R,S)
  IN  [x,y \in S |-> x=y \/ trcl[x,y]]





IsConnected(R, S) ==
  LET rtrcl == ReflexiveTransitiveClosure(R,S)
  IN  \A x,y \in S : rtrcl[x,y]

=============================================================================
