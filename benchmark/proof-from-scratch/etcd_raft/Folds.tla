------------------------------- MODULE Folds -------------------------------












MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==



















  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]


=============================================================================
