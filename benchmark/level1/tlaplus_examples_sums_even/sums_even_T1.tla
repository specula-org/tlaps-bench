------------------------- MODULE sums_even_T1 -------------------------
\* A proof that the sum x+x of the natural number x is always even.  

EXTENDS Naturals, TLAPS

Even(x) == x % 2 = 0
Odd(x) == x % 2 = 1

\* Z3 can solve it in a single step
THEOREM \A x \in Nat : Even(x+x)
  PROOF OMITTED

THEOREM T1 == \A x \in Nat: Even(x+x)
PROOF OBVIOUS

=============================================================================