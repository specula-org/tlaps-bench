------------------------------ MODULE bcastByz_FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ------------------------------

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

IndInv_Unforg_NoBcast_TLC ==  
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality( Corr ) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] /= "AC"
  /\ sent = {}  
  /\ rcvd \in [ Proc -> sent \cup SUBSET ByzMsgs ]   

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==  
  IndInv_Unforg_NoBcast_TLC => FCConstraints
PROOF OBVIOUS

=============================================================================

