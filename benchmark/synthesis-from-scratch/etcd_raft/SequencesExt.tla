---------------------------- MODULE SequencesExt ----------------------------
EXTENDS Sequences, Naturals, FiniteSets, FiniteSetsExt, Folds, Functions, Bags









LOCAL INSTANCE TLC
  
  
  

-----------------------------------------------------------------------------

  














ToSet(s) ==
  { s[i] : i \in DOMAIN s }





ToBag(s) ==
  [x \in Range(s) |-> Cardinality({i \in DOMAIN s : s[i] = x})]





SetToSeq(S) == 
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)






 

SetToSeqs(S) == 
  LET D == 1..Cardinality(S)
  IN { f \in [D -> S] : \A i,j \in D : i # j => f[i] # f[j] }





SetToSortSeq(S, op(_,_)) ==
  SortSeq(SetToSeq(S), op)










SetToAllKPermutations(S) ==
  UNION { SetToSeqs(s) : s \in SUBSET S  }




TupleOf(set, n) == 
  [1..n -> set]





SeqOf(set, n) == 
  UNION {[1..m -> set] : m \in 0..n}





BoundedSeq(S, n) ==
  SeqOf(S, n)

-----------------------------------------------------------------------------




Contains(s, e) ==
  \E i \in 1..Len(s) : s[i] = e





Reverse(s) ==
  [ i \in 1..Len(s) |-> s[(Len(s) - i) + 1] ]




Remove(s, e) ==
    SelectSeq(s, LAMBDA t: t # e)





ReplaceAll(s, old, new) ==
  [i \in 1 .. Len(s) |-> IF s[i] = old THEN new ELSE s[i]]

-----------------------------------------------------------------------------





SelectInSeq(seq, Test(_)) ==
  LET I == { i \in 1..Len(seq) : Test(seq[i]) }
  IN IF I # {} THEN Min(I) ELSE 0






SelectInSubSeq(seq, from, to, Test(_)) ==
  SelectInSeq(SubSeq(seq, from, to), Test)





SelectLastInSeq(seq, Test(_)) ==
  LET I == { i \in 1..Len(seq) : Test(seq[i]) }
  IN IF I # {} THEN Max(I) ELSE 0






SelectLastInSubSeq(seq, from, to, Test(_)) ==
  SelectLastInSeq(SubSeq(seq, from, to), Test)

-----------------------------------------------------------------------------













InsertAt(s, i, e) ==
  SubSeq(s, 1, i-1) \o <<e>> \o SubSeq(s, i, Len(s))




ReplaceAt(s, i, e) ==
  [s EXCEPT ![i] = e]
  



RemoveAt(s, i) == 
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))





RemoveFirst(s, e) ==
    IF \E i \in 1..Len(s): s[i] = e
    THEN RemoveAt(s, SelectInSeq(s, LAMBDA v: v = e))
    ELSE s





RemoveFirstMatch(s, Test(_)) ==
    IF \E i \in 1..Len(s): Test(s[i])
    THEN RemoveAt(s, SelectInSeq(s, Test))
    ELSE s

-----------------------------------------------------------------------------




Cons(elt, seq) == 
    <<elt>> \o seq







Snoc(elt, seq) == 
    Append(seq, elt)




Front(s) == 
  SubSeq(s, 1, Len(s)-1)




Last(s) ==
  s[Len(s)]

-----------------------------------------------------------------------------






IsPrefix(s, t) ==
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))




IsStrictPrefix(s,t) ==
  IsPrefix(s, t) /\ s # t






IsSuffix(s, t) ==
  IsPrefix(Reverse(s), Reverse(t))




IsStrictSuffix(s, t) ==
  IsSuffix(s,t) /\ s # t
  
-----------------------------------------------------------------------------




Prefixes(s) ==
  
  { SubSeq(s, 1, l) : l \in 0..Len(s) }




CommonPrefixes(S) ==
  LET P == UNION { Prefixes(seq) : seq \in S }
  IN { prefix \in P : \A t \in S: IsPrefix(prefix, t) }




LongestCommonPrefix(S) ==
  CHOOSE longest \in CommonPrefixes(S):  
          \A other \in CommonPrefixes(S):
              Len(other) <= Len(longest)




Suffixes(s) ==
  { SubSeq(s, l, Len(s)) : l \in 1..Len(s) } \cup {<<>>}

-----------------------------------------------------------------------------






SeqMod(a, b) == 
  IF a % b = 0 THEN b ELSE a % b













FoldSeq(op(_, _), base, seq) == 
  FoldFunction(op, base, seq)











FoldLeft(op(_, _), base, seq) == 
  MapThenFoldSet(LAMBDA x,y : op(y,x), base,
                 LAMBDA i : seq[i],
                 LAMBDA S : Max(S),
                 DOMAIN seq)











FoldRight(op(_, _), seq, base) == 
  MapThenFoldSet(op, base,
                 LAMBDA i : seq[i],
                 LAMBDA S : Min(S),
                 DOMAIN seq)



 

FoldLeftDomain(op(_, _), base, seq) == 
  FoldLeft(op, base, [i \in DOMAIN seq |-> i])





FoldRightDomain(op(_, _), seq, base) == 
  FoldRight(op, [i \in DOMAIN seq |-> i], base)

-----------------------------------------------------------------------------










FlattenSeq(seqs) ==
  IF Len(seqs) = 0 THEN seqs ELSE
    
    LET flatten[i \in 1..Len(seqs)] ==
        IF i = 1 THEN seqs[i] ELSE flatten[i-1] \o seqs[i]
    IN flatten[Len(seqs)]















Zip(s, t) ==
  LET l == IF Len(s) <= Len(t) THEN Len(s) ELSE Len(t)
  IN  [ i \in 1 .. l |-> <<s[i], t[i] >> ]












Interleave(s, t) ==
  CASE Len(s) = Len(t) /\ Len(s) > 0 ->
        LET u[ i \in 1..Len(s) ] == 
                IF i = 1 THEN << <<s[i]>> >> \o << <<t[i]>> >>
                ELSE u[i-1] \o << <<s[i]>> >> \o << <<t[i]>> >>
        IN Last(u)
    
    [] Len(s) = Len(t) /\ Len(s) = 0 -> << <<>>, <<>> >>





SubSeqs(s) ==
  { SubSeq(s, i+1, j) : i, j \in 0..Len(s) }














AllSubSeqs(s) ==
  { FoldFunction(Snoc, <<>>, [ i \in D |-> s[i] ]) : D \in SUBSET DOMAIN s }







IndexFirstSubSeq(s, t) ==
  LET last == CHOOSE i \in 0..Len(t) :
                /\ s \in SubSeqs(SubSeq(t, 1, i))
                /\ \A j \in 0..i-1 : s \notin SubSeqs(SubSeq(t, 1, j))
  IN last - (Len(s) - 1)





ReplaceSubSeqAt(i, r, s, t) ==
  LET prefix == SubSeq(t, 1, i - 1)
      suffix == SubSeq(t, i + Len(s), Len(t))
  IN prefix \o r \o suffix 




ReplaceFirstSubSeq(r, s, t) ==
  IF s \in SubSeqs(t)
  THEN ReplaceSubSeqAt(IndexFirstSubSeq(s, t), r, s, t)
  ELSE t













ReplaceAllSubSeqs(r, s, t) ==
  CASE s = t -> r
    [] r = s -> t  
    [] s # t /\ Len(s) = 0 ->
        LET z == Interleave([i \in 1..Len(t) |-> r], [i \in 1..Len(t) |-> <<t[i]>>])
        IN FlattenSeq(FlattenSeq(z))
    [] s # t /\ Len(s) > 0 /\ s \in SubSeqs(t) ->
        
        LET match(f) == { i \in 1..Len(f) : s = f[i] }
            comp(p, q) == \A i \in 1..Len(p) : p[i] <= q[i]
            
            
            
            
            R == BoundedSeq(BoundedSeq(Range(t), Len(t)), Len(t))
            
            S == { f \in R : FlattenSeq(f) = t }
            
            T == { f \in S : \A g \in S : 
                    Cardinality(match(g)) <= Cardinality(match(f)) }
            
            u == CHOOSE f \in T : 
                    \A g \in T : comp(
                        SetToSortSeq(match(f), <), SetToSortSeq(match(g), <))
        IN FlattenSeq([i \in 1..Len(u) |-> IF s = u[i] THEN r ELSE u[i]])
    [] OTHER -> t

=============================================================================
