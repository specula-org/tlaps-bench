---- MODULE TotalOrderQuantifierCheck ----
\* Isolated evaluation of TotalOrder, not of the full ZooKeeper spec.
EXTENDS Integers, Sequences, TLC

ZxidEqual(z1, z2) == z1[1] = z2[1] /\ z1[2] = z2[2]

TxnEqual(t1, t2) == /\ ZxidEqual(t1.zxid, t2.zxid)
                    /\ t1.value = t2.value

a == [zxid |-> <<1, 1>>, value |-> "a"]
b == [zxid |-> <<1, 2>>, value |-> "b"]
x == [zxid |-> <<9, 9>>, value |-> "x"]

TotalOrderHolds(h1, c1, h2, c2, requireTwoOnJ) ==
    LET antecedent == IF requireTwoOnJ THEN c1 >= 2 /\ c2 >= 2 ELSE c1 >= 2
    IN antecedent =>
       \A idx_i1 \in 1..(c1 - 1) : \A idx_i2 \in (idx_i1 + 1)..c1 :
         LET logOk == \E idx \in 1..c2 : TxnEqual(h1[idx_i2], h2[idx])
         IN \/ ~logOk
            \/ /\ logOk
               /\ \E idx_j2 \in 1..c2 :
                    /\ TxnEqual(h1[idx_i2], h2[idx_j2])
                    /\ \E idx_j1 \in 1..(idx_j2 - 1):
                         TxnEqual(h1[idx_i1], h2[idx_j1])

\* Witness delivered a before b. Other process delivered only b.
OldOnSingletonB == TotalOrderHolds(<<a, b>>, 2, <<b>>, 1, TRUE)
NewOnSingletonB == TotalOrderHolds(<<a, b>>, 2, <<b>>, 1, FALSE)

\* Other process delivered filler then b, never a.
OldOnXb == TotalOrderHolds(<<a, b>>, 2, <<x, b>>, 2, TRUE)
NewOnXb == TotalOrderHolds(<<a, b>>, 2, <<x, b>>, 2, FALSE)

\* Intended success.
NewOnAb == TotalOrderHolds(<<a, b>>, 2, <<a, b>>, 2, FALSE)

\* Other process never delivered b.
NewOnEmpty == TotalOrderHolds(<<a, b>>, 2, <<>>, 0, FALSE)

\* Witness has only one committed txn: no a-before-b pair.
NewOnSingletonWitness == TotalOrderHolds(<<b>>, 1, <<b>>, 1, FALSE)

ASSUME /\ OldOnSingletonB = TRUE
       /\ NewOnSingletonB = FALSE
       /\ OldOnXb = FALSE
       /\ NewOnXb = FALSE
       /\ NewOnAb = TRUE
       /\ NewOnEmpty = TRUE
       /\ NewOnSingletonWitness = TRUE

VARIABLE dummy
Init == dummy = 0
Next == UNCHANGED dummy
Spec == Init /\ [][Next]_dummy
====
