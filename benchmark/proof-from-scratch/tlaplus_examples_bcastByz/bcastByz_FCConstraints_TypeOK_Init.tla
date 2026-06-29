------------------------------ MODULE bcastByz_FCConstraints_TypeOK_Init ------------------------------

EXTENDS Naturals, 
        FiniteSets,
        Functions,
        FunctionTheorems, 
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS
        
CONSTANTS N, T, F

VARIABLE Corr           
VARIABLE Faulty         

VARIABLE pc             
VARIABLE rcvd           
VARIABLE sent           
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N          
M == { "ECHO" }

ByzMsgs == Faulty \X M

Init == 
  /\ sent = {}                          
  /\ pc \in [ Proc -> {"V0", "V1"} ]    
  /\ rcvd = [ i \in Proc |-> {} ]       
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F          
  /\ Faulty = Proc \ Corr                 

TypeOK == 
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]          
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M     
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

FCConstraints == 
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ IsFiniteSet(Corr)
  /\ IsFiniteSet(Faulty)
  /\ Corr \cup Faulty = Proc 
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T   
  /\ ByzMsgs \subseteq Proc \X M     
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)        

THEOREM FCConstraints_TypeOK_Init == 
  Init => FCConstraints /\ TypeOK
PROOF OBVIOUS

=============================================================================

