------------------------------- MODULE EWD998PCal -------------------------------

EXTENDS Integers, Bags, BagsExt

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0} 

Node == 0 .. N-1

Initiator == 0 

VARIABLE network

VARIABLES active, color, counter

Init == 
        /\ network = [n \in Node |-> IF n = Initiator THEN SetToBag({[type|-> "tok", q |-> 0, color |-> "black"]}) ELSE EmptyBag]
        
        /\ active \in [Node -> BOOLEAN]
        /\ color = [self \in Node |-> "black"]
        /\ counter = [self \in Node |-> 0]

-----------------------------------------------------------------------------

token ==
    LET tpos == CHOOSE i \in Node : \E m \in DOMAIN network[i]: m.type = "tok"
        tok == CHOOSE m \in DOMAIN network[tpos] : m.type = "tok"
    IN [pos |-> tpos, q |-> tok.q, color |-> tok.color]

pending ==
    [n \in Node |-> IF [type|->"pl"] \in DOMAIN network[n] THEN network[n][[type|->"pl"]] ELSE 0]

EWD998 == INSTANCE EWD998

-----------------------------------------------------------------------------

=============================================================================
