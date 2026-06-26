------------------------- MODULE sums_even_T1 -------------------------

EXTENDS Naturals, TLAPS

Even(x) == x % 2 = 0

THEOREM T1 == \A x \in Nat: Even(x+x)
PROOF OBVIOUS

=============================================================================

