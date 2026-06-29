------------------------------ MODULE BagsExt ------------------------------


















LOCAL INSTANCE Bags
LOCAL INSTANCE Integers
LOCAL INSTANCE Folds













BagAdd(B, x) ==
   IF x \in DOMAIN B
   THEN [e \in DOMAIN B |-> IF e=x THEN B[e]+1 ELSE B[e]]
   ELSE [e \in DOMAIN B \union {x} |-> IF e=x THEN 1 ELSE B[e]]















BagRemove(B,x) ==
   IF x \in DOMAIN B
   THEN IF B[x] = 1
        THEN [e \in DOMAIN B \ {x} |-> B[e]]
        ELSE [e \in DOMAIN B |-> IF e=x THEN B[e]-1 ELSE B[e]]
   ELSE B











BagRemoveAll(B,x) ==
   [e \in DOMAIN B \ {x} |-> B[e]]
 



























 MapThenFoldBag(op(_,_), base, f(_), choose(_), B) ==
    LET handle(x) ==  
        LET pow[n \in Nat \ {0}] ==
            op(IF n=1 THEN base ELSE pow[n-1], f(x))
        IN  pow[B[x]]
    IN  MapThenFoldSet(op, base, handle,
                       LAMBDA S : CHOOSE x \in S : TRUE,
                       DOMAIN B)










FoldBag(op(_,_), base, B) ==
   MapThenFoldBag(op, base, LAMBDA x: x, LAMBDA S : CHOOSE x \in S : TRUE, B)




SumBag(B) ==
   FoldBag(LAMBDA x,y : x+y, 0, B)




ProductBag(B) ==
   FoldBag(LAMBDA x,y : x*y, 1, B)

=============================================================================
