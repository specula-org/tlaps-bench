---- MODULE LPOQuantifierCheck ----
\* Isolated evaluation of LocalPrimaryOrder, not of the full ZooKeeper spec.
EXTENDS Integers, FiniteSets, Sequences, TLC

ZxidCompare(z1, z2) == \/ z1[1] > z2[1]
                       \/ /\ z1[1] = z2[1]
                          /\ z1[2] > z2[2]

ZxidEqual(z1, z2) == z1[1] = z2[1] /\ z1[2] = z2[2]

TxnEqual(t1, t2) == /\ ZxidEqual(t1.zxid, t2.zxid)
                    /\ t1.value = t2.value

a == [zxid |-> <<1, 1>>, value |-> "a"]
b == [zxid |-> <<1, 2>>, value |-> "b"]
x == [zxid |-> <<9, 9>>, value |-> "x"]

txn_set == {a, b}

OrderHolds(history, committed, TxnPre, TxnNext, requireTwo) ==
    LET deliveredNext == \E idx \in 1..committed: TxnEqual(history[idx], TxnNext)
        consequent == \E idx2 \in 1..committed:
                        /\ TxnEqual(history[idx2], TxnNext)
                        /\ idx2 > 1
                        /\ \E idx1 \in 1..(idx2 - 1):
                             TxnEqual(history[idx1], TxnPre)
        antecedent == IF requireTwo
                      THEN committed >= 2 /\ deliveredNext
                      ELSE deliveredNext
    IN antecedent => consequent

PairOrder(history, committed, requireTwo) ==
    \A txn1, txn2 \in txn_set:
        \/ TxnEqual(txn1, txn2)
        \/ /\ ~TxnEqual(txn1, txn2)
           /\ LET TxnPre  == IF ZxidCompare(txn1.zxid, txn2.zxid) THEN txn2 ELSE txn1
                  TxnNext == IF ZxidCompare(txn1.zxid, txn2.zxid) THEN txn1 ELSE txn2
              IN OrderHolds(history, committed, TxnPre, TxnNext, requireTwo)

\* Broadcasts a then b. Follower delivered only b.
OldOnSingletonB == PairOrder(<<b>>, 1, TRUE)
NewOnSingletonB == PairOrder(<<b>>, 1, FALSE)

\* Follower delivered filler then b, never a.
OldOnXb == PairOrder(<<x, b>>, 2, TRUE)
NewOnXb == PairOrder(<<x, b>>, 2, FALSE)

\* Intended success: delivered a then b.
NewOnAb == PairOrder(<<a, b>>, 2, FALSE)

ASSUME /\ OldOnSingletonB = TRUE
       /\ NewOnSingletonB = FALSE
       /\ OldOnXb = FALSE
       /\ NewOnXb = FALSE
       /\ NewOnAb = TRUE

VARIABLE dummy
Init == dummy = 0
Next == UNCHANGED dummy
Spec == Init /\ [][Next]_dummy
====
