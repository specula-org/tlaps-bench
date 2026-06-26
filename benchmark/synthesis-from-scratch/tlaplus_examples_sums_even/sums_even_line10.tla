------------------------- MODULE sums_even_line10 -------------------------

EXTENDS Naturals, TLAPS

Even(x) == x % 2 = 0

THEOREM \A x \in Nat : Even(x+x)
PROOF OBVIOUS

=============================================================================

