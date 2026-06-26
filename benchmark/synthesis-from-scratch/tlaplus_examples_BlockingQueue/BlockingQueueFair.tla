------------------------- MODULE BlockingQueueFair -------------------------
EXTENDS Naturals, Sequences, FiniteSets, Functions, SequencesExt

CONSTANTS Producers,   
          Consumers,   
          BufCapacity  

ASSUME Assumption ==
       /\ Producers # {}                      
       /\ Consumers # {}                      
       /\ Producers \intersect Consumers = {} 
       /\ Consumers \intersect Producers = {} 
       /\ BufCapacity \in (Nat \ {0})         
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSeqC, waitSeqP
vars == <<buffer, waitSeqC, waitSeqP>>

WaitingThreads == Range(waitSeqC) \cup Range(waitSeqP)

RunningThreads == (Producers \cup Consumers) \ WaitingThreads

NotifyOther(ws) ==
            \/ /\ ws = <<>>
               /\ UNCHANGED ws
            \/ /\ ws # <<>>
               /\ ws' = Tail(ws)

Wait(ws, t) == 
            /\ ws' = Append(ws, t)
            /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
/\ t \notin Range(waitSeqP)
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(waitSeqC)
      /\ UNCHANGED waitSeqP
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(waitSeqP, t)
      /\ UNCHANGED waitSeqC
      
Get(t) ==
/\ t \notin Range(waitSeqC)
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(waitSeqP)
      /\ UNCHANGED waitSeqC
   \/ /\ buffer = <<>>
      /\ Wait(waitSeqC, t)
      /\ UNCHANGED waitSeqP

-----------------------------------------------------------------------------

Init == /\ buffer = <<>>
        /\ waitSeqC = <<>>
        /\ waitSeqP = <<>>

Next == \/ \E p \in Producers: Put(p, p) 
        \/ \E c \in Consumers: Get(c)

Spec == Init /\ [][Next]_vars 

FairSpec == Spec /\ \A c \in Consumers : WF_vars(Get(c)) 
                 /\ \A p \in Producers : WF_vars(Put(p, p)) 

----------------

BQS == INSTANCE BlockingQueueSplit WITH waitSetC <- Range(waitSeqC), 
                                        waitSetP <- Range(waitSeqP)

BQSSpec == BQS!Spec
THEOREM Spec => BQSSpec
  PROOF OMITTED

BQSFairSpec == BQS!A!FairSpec
THEOREM FairSpec => BQSFairSpec
  PROOF OMITTED

BQSStarvation == BQS!A!Starvation
THEOREM FairSpec => BQSStarvation
  PROOF OMITTED

-----------------------------------------------------------------------------

TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           
           /\ waitSeqP \in Seq(Producers)
           /\ IsInjective(waitSeqP) 
           
           /\ waitSeqC \in Seq(Consumers)
           /\ IsInjective(waitSeqC) 

=============================================================================
