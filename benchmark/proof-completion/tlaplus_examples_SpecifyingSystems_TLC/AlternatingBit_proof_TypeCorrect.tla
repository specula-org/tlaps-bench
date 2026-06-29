------------------------ MODULE AlternatingBit_proof_TypeCorrect -----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM ABSpec => []ABTypeInv                                         *)
(* stated in AlternatingBit.tla.                                           *)
(***************************************************************************)
EXTENDS AlternatingBit, TLAPS

LEMMA AppendType ==
  ASSUME NEW T, NEW s \in Seq(T), NEW e \in T
  PROVE  Append(s, e) \in Seq(T)
  OBVIOUS

LEMMA TailType ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Tail(s) \in Seq(T)
  OBVIOUS

LEMMA HeadType ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Head(s) \in T
  OBVIOUS

LEMMA LosePreservesType ==
  ASSUME NEW T, NEW q \in Seq(T), q # << >>,
         NEW i \in 1..Len(q),
         NEW q2,
         q2 = [j \in 1..(Len(q)-1) |-> IF j < i THEN q[j] ELSE q[j+1]]
  PROVE  q2 \in Seq(T)
  OBVIOUS

THEOREM TypeCorrect == ABSpec => []ABTypeInv
PROOF OBVIOUS

============================================================================
