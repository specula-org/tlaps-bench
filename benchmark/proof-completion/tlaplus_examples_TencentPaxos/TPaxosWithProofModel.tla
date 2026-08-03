------------------------------ MODULE TPaxosWithProofModel --------------------------------

EXTENDS Integers, FiniteSets, TLAPS
Max(m, n) == IF m > n THEN m ELSE n
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])
CONSTANTS
    Participant,  
    Value         

None == CHOOSE b : b \notin Value

=============================================================================
