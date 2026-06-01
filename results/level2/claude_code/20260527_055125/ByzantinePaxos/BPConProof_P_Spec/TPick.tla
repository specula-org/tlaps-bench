------------------------------- MODULE TPick -------------------------------
EXTENDS Integers, TLAPS

Cond(S, c, vv) == \E m \in S : /\ m.bal = 0
                              /\ m.mbal =< c
                              /\ (m.mbal = c) => (m.mval = vv)

\* derive atomic existence via negation
LEMMA TWit ==
  ASSUME NEW S, NEW c \in Int, NEW vv, Cond(S, c, vv)
  PROVE  \E m \in S : m.bal = 0 /\ m.mbal =< c
<1> SUFFICES ASSUME \A m \in S : ~(m.bal = 0 /\ m.mbal =< c) PROVE FALSE
  OBVIOUS
<1>. QED BY DEF Cond

\* value via negation/forall form
LEMMA TVal ==
  ASSUME NEW S, NEW c \in Int, NEW vv, Cond(S, c, vv),
         \A m \in S : m.mbal = c \/ m.bal # 0   \* dummy
  PROVE  \E m \in S : m.bal = 0 /\ m.mbal =< c /\ (m.mbal = c => m.mval = vv)
  BY DEF Cond

=============================================================================
