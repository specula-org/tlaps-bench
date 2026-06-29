------------------------- MODULE sums_even_T1 -------------------------
\* A proof that the sum x+x of the natural number x is always even.  

EXTENDS Naturals, TLAPS

Even(x) == x % 2 = 0
Odd(x) == x % 2 = 1

\* Z3 can solve it in a single step
THEOREM \A x \in Nat : Even(x+x)
PROOF OMITTED

\* alternatively we prove this step-wise by making a case distinction on x being even or odd
THEOREM T1 == \A x \in Nat: Even(x+x)
PROOF OBVIOUS

=============================================================================
\* Modification History
\* Last modified Tue Mar 08 11:49:27 CET 2016 by marty
\* Created Mon Oct 26 15:01:26 CET 2015 by marty
