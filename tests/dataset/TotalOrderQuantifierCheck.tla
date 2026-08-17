---- MODULE TotalOrderQuantifierCheck ----
\* Isolated evaluation of TotalOrder, not of the full ZooKeeper spec.
EXTENDS Integers, Sequences, TLC

ZxidEqual(z1, z2) == z1[1] = z2[1] /\ z1[2] = z2[2]

TxnEqual(t1, t2) == /\ ZxidEqual(t1.zxid, t2.zxid)
                    /\ t1.value = t2.value

setup == [zxid |-> <<0, 1>>, value |-> "setup"]
a == [zxid |-> <<1, 1>>, value |-> "a"]
b == [zxid |-> <<1, 2>>, value |-> "b"]

TotalOrderHolds(h1, c1, h2, c2) ==
    c1 >= 2 /\ c2 >= 2 =>
       \A idx_i1 \in 1..(c1 - 1) : \A idx_i2 \in (idx_i1 + 1)..c1 :
         LET logOk == \E idx \in 1..c2 : TxnEqual(h1[idx_i2], h2[idx])
         IN \/ ~logOk
            \/ /\ logOk
               /\ \E idx_j2 \in 1..c2 :
                    /\ TxnEqual(h1[idx_i2], h2[idx_j2])
                    /\ \E idx_j1 \in 1..(idx_j2 - 1):
                         TxnEqual(h1[idx_i1], h2[idx_j1])

\* Without the modeled setup prefix, the two-entry guard skips <<b>>.
UninitializedSingletonSkipped == TotalOrderHolds(<<a, b>>, 2, <<b>>, 1)

\* With the shared setup prefix, the same bad update order is checked.
InitializedSingletonCaught == TotalOrderHolds(<<setup, a, b>>, 3, <<setup, b>>, 2)

\* Intended success: both processes deliver setup, a, then b.
InitializedOrderHolds == TotalOrderHolds(<<setup, a, b>>, 3, <<setup, a, b>>, 3)

\* The other process delivered only the setup transaction, not b.
SetupOnlyHolds == TotalOrderHolds(<<setup, a, b>>, 3, <<setup>>, 1)

ASSUME /\ UninitializedSingletonSkipped = TRUE
       /\ InitializedSingletonCaught = FALSE
       /\ InitializedOrderHolds = TRUE
       /\ SetupOnlyHolds = TRUE

VARIABLE dummy
Init == dummy = 0
Next == UNCHANGED dummy
Spec == Init /\ [][Next]_dummy
====
