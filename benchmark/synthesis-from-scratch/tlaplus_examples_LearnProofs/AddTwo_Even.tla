------------------------------ MODULE AddTwo_Even --------------------------------

EXTENDS AddTwo

a|b == \E c \in Nat : a*c = b

Even == 2|x

THEOREM Spec => []Even
PROOF OBVIOUS

=============================================================================

