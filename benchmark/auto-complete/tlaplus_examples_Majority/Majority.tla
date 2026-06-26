-------------------------------- MODULE Majority -----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT Value
ASSUME ConstAssump == Value # {}

VARIABLES 
  seq,    
  i,      
  cand,   
  cnt     

vars == <<seq, i, cand, cnt>>

TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in 1 .. Len(seq)+1
    /\ cand \in Value
    /\ cnt \in Nat

Init ==
    /\ seq \in Seq(Value)
    /\ i = 1
    /\ cand \in Value
    /\ cnt = 0

Next ==
    /\ i <= Len(seq)
    /\ i' = i+1 /\ seq' = seq
    /\ \/ /\ cnt = 0
          /\ cand' = seq[i]
          /\ cnt' = 1
       \/ /\ cnt # 0 /\ cand = seq[i]
          /\ cand' = cand
          /\ cnt' = cnt + 1
       \/ /\ cnt # 0 /\ cand # seq[i]
          /\ cand' = cand
          /\ cnt' = cnt - 1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

PositionsBefore(v,j) == { k \in 1 .. (j-1) : seq[k] = v }

OccurrencesBefore(v,j) == Cardinality(PositionsBefore(v,j))

Occurrences(x) == OccurrencesBefore(x, Len(seq)+1)

Correct == 
    i > Len(seq) =>
    \A v \in Value : 2 * Occurrences(v) > Len(seq) => v = cand

Inv ==
    /\ cnt <= OccurrencesBefore(cand, i)
    /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

==============================================================================
