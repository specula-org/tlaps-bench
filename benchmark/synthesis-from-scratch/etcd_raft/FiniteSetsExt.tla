--------------------------- MODULE FiniteSetsExt ---------------------------
EXTENDS Integers, FiniteSets, Folds, Functions 









FoldSet(op(_,_), base, set) ==
   MapThenFoldSet(op, base, LAMBDA x : x, LAMBDA s : CHOOSE x \in s : TRUE, set)







SumSet(set) ==
   FoldSet(+, 0, set)







ProductSet(set) ==
   FoldSet(LAMBDA x, y: x * y, 1, set)





ReduceSet(op(_, _), set, acc) == 
   FoldSet(op, acc, set)










MapThenSumSet(op(_), set) ==
   MapThenFoldSet(+, 0, op, LAMBDA s : CHOOSE x \in s : TRUE, set)














FlattenSet(S) ==
   UNION S













SymDiff(A, B) == (A \ B) \cup (B \ A)

-----------------------------------------------------------------------------











Quantify(S, P(_)) ==
   Cardinality({s \in S : P(s)})

-----------------------------------------------------------------------------














kSubset(k, S) == 
   { s \in SUBSET S : Cardinality(s) = k }

-----------------------------------------------------------------------------





Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

-----------------------------------------------------------------------------



















Choices(Sets) == LET ChoiceFunction(Ts) == { f \in [Ts -> UNION Ts] : 
                                               \A T \in Ts : f[T] \in T }
                 IN  { Range(f) : f \in ChoiceFunction(Sets) }

-----------------------------------------------------------------------------














ChooseUnique(S, P(_)) == CHOOSE x \in S :
                              P(x) /\ \A y \in S : P(y) => y = x

=============================================================================
