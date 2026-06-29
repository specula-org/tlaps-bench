------------------------------ MODULE bcastByz_Unforg_Step3 ------------------------------

(* TLA+ encoding of a parameterized model of the broadcast distributed  
   algorithm with Byzantine faults.
  
   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:
  
   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94
                                                             
   A short description of the parameterized model is described in: Gmeiner,   
   Annu, et al. "Tutorial on parameterized model checking of fault-tolerant   
   distributed algorithms." International School on Formal Methods for the  
   Design of Computer, Communication and Software Systems. Springer  
   International Publishing, 2014.                   
  
   This specification has a TLAPS proof for property Unforgeability: if process p 
   is correct and does not broadcast a message m, then no correct process ever 
   accepts m. The formula InitNoBcast represents that the transmitter does not 
   broadcast any message. So, our goal is to prove the  formula
        (InitNoBcast /\ [][Next]_vars) => []Unforg                    
  
   We can use TLC to check two properties (for fixed parameters N, T, and F):
    - Correctness: if a correct process broadcasts, then every correct process accepts,
    - Replay: if a correct process accepts, then every correct process accepts.  
  
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
 *)

EXTENDS bcastByz

                        (* Corr and Faulty are declared as variables since we want to 
                           check all possible cases. And after the initial step, Corr
                           and Faulty are unchanged. *)

(* ByzMsgs == { <<p, "ECHO">> : p \in Faulty }: quite complicated to write a TLAPS proof 
   for the cardinality of the expression { e : x \in S}
 *)

(* Instead of modeling a broadcaster explicitly, two initial values V0 and V1 at correct
   processes are used to model whether a process has received the INIT message from the
   broadcaster or not, respectively. Then the precondition of correctness can be modeled 
   that all correct processes initially have value V1, while the precondition of unforgeability  
   that all correct processes initially have value V0.
 *)
        
(* This formula specifies restricted initial states: all correct processes initially have value V0.
   (This corresponds to the case when no correct process received an INIT message from a broadcaster.)
   Notice that in our modeling Byzantine processes also start in the local state V0.
 *)

(* A correct process can receive all ECHO messages sent by the other correct processes,
   i.e., a subset of sent, and all possible ECHO messages from the Byzantine processes,
   i.e., a subset of ByzMsgs. If includeByz is FALSE, the messages from the Byzantine
   processes are not included.
 *)

ReceiveFromCorrectSender(self) == Receive(self, FALSE)

(* The first if-then expression in Figure 7 [1]: If process p received an INIT message and
   did not send <ECHO> before, then process p sends ECHO to all.
 *)

(* The 3rd if-then expression in Fig. 7 [1]: If correct process p received ECHO messages 
   from at least N - 2*T distinct processes and did not send ECHO before, then process p sends
   ECHO messages to all. 
  
   Since processes send only ECHO messages, the number of messages in rcvd[self] equals the   
   number of distinct processes from which process self received ECHO messages. 
  
   The 3rd conjunction "Cardinality(rcvd'[self]) < N - T" ensures that process p cannot accept
   or not execute the 2nd if-then expression in Fig. 7 [1]. If process p received ECHO messages
   from at least N - T distinct processes, the formula UponAcceptNotSentBefore is called.
 *)         
        
(* The 2nd and 3rd if-then expressions in Figure 7 [1]: If process p received <ECHO> from at 
   least N - T distinct processes and did not send ECHO message before, then process p accepts       
   and sends <ECHO> to all.                  
 *)        
        
(* Only the 2nd if-then expression in Fig. 7 [1]:  if process p sent ECHO messages and received 
   ECHO messages from at least N - T distinct processes, it accepts.
  
   As pc[self] = "SE", the 3rd if-then expression cannot be executed.
 *)        

(* All possible process steps.*)                

(* Some correct process does a transition step.*)                         

(* Add weak fairness condition since we want to check liveness properties. We require that 
   if UponV1 (or UponNonFaulty, UponAcceptNotSentBefore, UponAcceptSentBefore) ever becomes 
   forever enabled, then this step must eventually occur.      
 *)
Spec == Init /\ [][Next]_vars 
             /\ WF_vars(\E self \in Corr: /\ ReceiveFromCorrectSender(self)
                                          /\ \/ UponV1(self)
                                             \/ UponNonFaulty(self)
                                             \/ UponAcceptNotSentBefore(self)
                                             \/ UponAcceptSentBefore(self))

(* This formula SpecNoBcast is used to only check Unforgeability.
   No fairness is needed, as Unforgeability is a safety property.
 *)

(* V0 - the initial state when process p doesn't receive an INIT message
   V1 - the initial state when process p receives an INIT message
   SE - the state when process p sends ECHO messages but doesn't accept 
   AC - the accepted state when process p accepts            
 *) 
TypeOK == 
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]          
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M     
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

(* Constraints about the cardinalities of Faulty and Corr, their elements, and the upper bound  
   of the set of possible Byzantine messages. The FCConstraints is an invariant. One can probably
   prove the theorems below without FCConstraints (by applying facts from FiniteSetTheorems), 
   but these proofs will be longer.
 *)          
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
          
(****************************** SPECIFICATION ******************************)

(* If a correct process broadcasts, then every correct process eventually accepts. *)
CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\A i \in Corr: pc[i] = "AC")

(* If a correct process accepts, then every correct process accepts. *)
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))

(* If no correct process don't broadcast ECHO messages then no correct processes accept. *)  
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] /= "AC")

(* The special case of the unforgeability property. When our algorithms start with InitNoBcast,
   we can rewrite UnforgLtl as a first-order formula.     
 *)          
Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC")) 

(* A typical proof for proving a safety property in TLA+ is to show inductive invariance:
      1/ Init => IndInv
      2/ IndInv /\ [Next]_vars => IndInv'
      3/ IndInv => Safety
  
   Therefore, finding an inductive invariant is one of the most important and difficult step
   in writing a full formal proof. Here, Safety is Unforgeability and the corresponding indutive
   invariant is IndInv_Unforg_NoBcast. I started with TypeOK and Safety, and then tried to add  
   new constraints (inductive strengthens) in order to have the inductive invariant. In this 
   example, additional constraints are  relationships between the number of messages, pc, and 
   the number of faulty processes.    
 *)                
IndInv_Unforg_NoBcast ==  
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}  
  /\ pc = [ i \in Proc |-> "V0" ]

(* Before doing an actual proof with TLAPS, we want to check the invariant candidate with TLC
   (for fixed parameters). One can do so by running depth-first search with TLC by setting 
   depth to 2.  
  
   Unfortunately, checking Spec_IIU1 with TLC still takes too several hours even in small cases.
   The main reason is that the order of subformulas in IndInv_Unforg_NoBcast makes TLC consider
   unnecessary values and generate an enormous number of initial states which are unreachable 
   in SpecNoBcast. For example, in order to evaluate the subformula in IndInv_Unforg_NoBcast
          pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ],       
   TLC needs to generate and consider (2^{Card(Proc)})^4 cases. However, most of them are 
   elimitated by the last constraint pc = [ i \in Proc |-> "V0" ].
  
   Therefore, it is better to use the following formula IndInv_Unforg_NoBcast_TLC which is 
   obtained by rearranging the order of subformulas in IndInv_Unforg_NoBcast and eliminating
   duplicant constraints. Notice that in order to check an inductive invariant, we need to 
   consider only executions which have only one transition step. Therefore, in the advanced 
   settings of the TLC model checker, we can set the depth of executions to 2.                                                        
 *)   
IndInv_Unforg_NoBcast_TLC ==  
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality( Corr ) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] /= "AC"
  /\ sent = {}  
  /\ rcvd \in [ Proc -> sent \cup SUBSET ByzMsgs ]   

(******************************* TLAPS PROOFS ******************************)      
 
(* The constraints between N, T, and F*)
THEOREM NTFRel == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0) /\ N - 2*T >= T + 1
PROOF OMITTED
  
(* Proc is always a finite set and its cardinality is N*)  
 THEOREM ProcProp == Cardinality(Proc) = N /\ IsFiniteSet(Proc) /\ Cardinality(Proc) \in Nat
PROOF OMITTED

(* If we have 
      1/ X, Y, and Z are finite,
      2/ X and Y are disjoint, and
      3/ the union of X and Y is Z,
   then we have the sum of Card(X) and Card(Y) is Card(Z).*)   
THEOREM UMFS_CardinalityType == 
  \A X, Y, Z :    
        /\ IsFiniteSet(X) 
        /\ IsFiniteSet(Y) 
        /\ IsFiniteSet(Z) 
        /\ X \cup Y = Z
        /\ X = Z \ Y
     => Cardinality(X) = Cardinality(Z) - Cardinality(Y)
PROOF OMITTED
       
(* In the following, we try to prove that 
      1/ FCConstraints, TypeOK and IndInv_Unforg_NoBcastare inductive invariants, and
      2/ IndInv_Unforg_NoBcast implies Unforg.
  
   A template proof for an inductive invariant Spec => IndInv is
      1. Init => IndInv
      2. IndInv /\ [Next]_vars => IndInv'
          2.1 IndInv /\ Next => IndInv'
          2.2 IndInv /\ UNCHANGED vars => IndInv'
      3. IndInv => Safety
      4. Spec => []Safety  
   Some adivces:
      - Rewrite Next (or Step) as much as possible.
      - Rewrite IndInv' such that the primed operator appears only after constants or variables.
      - Remember to use a constraint Cardinality(X) \in Nat for some finite set X when reasoning
        about the cardinality.        
      - Different strings are not equivalent.
   Some practical hints:
      - Rewrite formulas into CNF or DNF forms.
      - Rewrite IndInv' such that the primed operator appears only after constants or variables.
      - Remember to use a constraint Cardinality(X) \in Nat for some finite set X 
        when reasoning about the cardinality.        
      - Different strings are not equivalent. 
 *)

(* FCConstraints /\ TypeOK is an inductive invariant of SpecNoBcast. Notice that only TypeOK is  
   also an inductive invariant. 
   InitNoBcast => FCConstraints /\ TypeOK 
 *)    
THEOREM FCConstraints_TypeOK_InitNoBcast == 
  InitNoBcast => FCConstraints /\ TypeOK
PROOF OMITTED
    
THEOREM FCConstraints_TypeOK_Init == 
  Init => FCConstraints /\ TypeOK
PROOF OMITTED

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast ==  
  IndInv_Unforg_NoBcast => FCConstraints /\ TypeOK
PROOF OMITTED

(* We write this proof to ensure that the way we check our inductive invariant with TLC is 
   correct. The description of Init0 is mentioned in the comments of IndInv_Unforg_NoBcast_TLC.      
 *)
THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==  
  IndInv_Unforg_NoBcast_TLC => FCConstraints
PROOF OMITTED

THEOREM FCConstraints_TypeOK_Next ==
  FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
PROOF OMITTED
        
THEOREM FCConstraints_TypeOK_SpecNoBcast == SpecNoBcast => [](FCConstraints /\ TypeOK)
PROOF OMITTED

(* The following is the main part of our proof. We prove that IndInv_Unforg_NoBcast is an
   inductive invariant.
  
   Step 1: Init => IndInv
 *)  
THEOREM Unforg_Step1 == InitNoBcast => IndInv_Unforg_NoBcast   
PROOF OMITTED
    
(* Step 2: IndInv /\ Next => IndInv' and a proof for stuttering steps *)     
THEOREM Unforg_Step2 == IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
PROOF OMITTED
  
(* Step 3: IndInv => Safety *)   
THEOREM Unforg_Step3 == IndInv_Unforg_NoBcast=> Unforg
PROOF OBVIOUS

(* Step 4: Spec => []Safety *)    
        
=============================================================================
\* Modification History
\* Last modified Sat Sep 04 19:49:08 CEST 2021 by tran

